--- Object tagging components.

--
-- Permission is hereby granted, free of charge, to any person obtaining
-- a copy of this software and associated documentation files (the
-- "Software"), to deal in the Software without restriction, including
-- without limitation the rights to use, copy, modify, merge, publish,
-- distribute, sublicense, and/or sell copies of the Software, and to
-- permit persons to whom the Software is furnished to do so, subject to
-- the following conditions:
--
-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
-- MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
-- IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
-- CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
-- TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
-- SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
--
-- [ MIT license: http://www.opensource.org/licenses/mit-license.php ]
--

-- Standard library imports --
local assert = assert
local ipairs = ipairs
local pairs = pairs
local type = type

-- Modules --
local adaptive = require("tektite_core.table.adaptive")
local array_funcs = require("tektite_core.array.funcs")
local class = require("tektite_core.class")
local iterator_utils = require("iterator_ops.utils")

-- Unique member keys (Sublink) --
local _can_link = {}
local _interfaces = {}
local _link_to = {}
local _name = {}

-- Unique member keys (Tags) --
local _implemented_by = {}
local _implies = {}
local _tags = {}

--
local IterStrList = iterator_utils.InstancedAutocacher(function()
	local str_list = {}

	-- Body --
	return function(_, i)
		return i + 1, str_list[i + 1]
	end,

	-- Done --
	function(_, i)
		return str_list[i + 1] == nil
	end,

	-- Setup --
	function(T, enum, name_, as_set)
		--
		local count = 0

		if as_set then
			for base in adaptive.IterSet(name_) do
				count = enum(T, str_list, base, count)
			end
		else
			for _, base in adaptive.IterArray(name_) do
				count = enum(T, str_list, base, count)
			end
		end

		-- Enumeration will overwrite the old elements, but if the previous iteration was
		-- longer than this one, the list will still contain leftover elements at the tail
		-- end, so trim the list as needed. Remove any duplicates to get the final list.
		for i = #str_list, count + 1, -1 do
			str_list[i] = nil
		end

		array_funcs.RemoveDups(str_list)

		return nil, 0
	end
end)

-- Tags class definition --
return class.Define(function(Tags)
	-- Forward references --
	local Children, Is, Parents, TagAndChildren

	-- Helper to resolve tags during iteration
	local function Name (tag, i)
		local name = tag and tag[i]

		if name then
			return i, name
		end
	end

	do
		-- Iterator body
		local function AuxChildren (tag, i)
			return Name(tag, i + 1)
		end

		--- Iterator.
		-- @string name Tag name.
		-- @treturn iterator Supplies, in order, at each iteration:
		--
		-- * Iteration variable, of dubious practical use.
		-- * Child tag name, s.t. _name_ was assigned as a parent in @{Tags:New}. (Grandchildren,
		-- et al. are **not** iterated.)
		function Tags:Children (name)
			local tag = self[_tags][name]

			return AuxChildren, tag, tag and tag.nparents or -1
		end
	end

	--- Predicate.
	-- @string name Tag name.
	-- @treturn boolean The name has been registered with @{Tags:New}?
	function Tags:Exists (name)
		return self[_tags][name] ~= nil
	end

	-- Helper to distinguish prospective property keys
	local function IsProp (what)
		return type(what) == "string" and what ~= "sub_links"
	end

	--- DOCME
	-- @string name
	-- @string what
	-- @return
	function Tags:GetProperty (name, what)
		local tag = self[_tags][name]

		if tag and IsProp(what) then
			return tag[what]
		else
			return nil
		end
	end

	do
		--
		local function AuxHasChild (T, name, child)
			for _, tname in Children(T, name) do
				if tname == child or AuxHasChild(T, tname, child) then
					return true
				end
			end

			return false
		end

		--- DOCME
		-- @function Tags:HasChild
		-- @string name
		-- @string cname
		-- @treturn boolean
		Tags.HasChild = AuxHasChild
	end

	do
		--
		local function AuxHasSublink (T, name, sub)
			--
			local sub_links = T[_tags][name].sub_links

			if sub_links then
				local sublink = sub_links[sub]

				if sublink then
					return sublink
				end
			end

			--
			for _, tname in Parents(T, name) do
				local sublink = AuxHasSublink(T, tname, sub)

				if sublink then
					return sublink
				end
			end
		end

		-- --
		local Name1, Sub1, Sublink1
		local Name2, Sub2, Sublink2

		--
		local function FindSublink (T, name, sub)
			if name == Name1 and sub == Sub1 then
				return Sublink1
			elseif name == Name2 and sub == Sub2 then
				return Sublink2
			else
				local sublink = AuxHasSublink(T, name, sub)

				Name1, Sub1, Sublink1 = name, sub, sublink
				Name2, Sub2, Sublink2 = Name1, Sub1, Sublink1

				return sublink
			end
		end

		--- DOCME
		function Tags:CanLink (name1, name2, object1, object2, sub1, sub2)
			local so1, is_cont, passed, why = FindSublink(self, name1, sub1), true

			if so1 then
				local so2 = FindSublink(self, name2, sub2)

				if so2 then
					passed, why, is_cont = so1[_can_link](object1, object2, so1, so2) --- ????
				else
					why = "Missing sublink #2: `" .. (sub2 or "?") .. "`"
				end
			else
				why = "Missing sublink #1: `" .. (sub1 or "?") .. "`"
			end

			if passed then
				return true
			else
				return false, why or "", not not is_cont
			end
		end

		--- DOCME
		-- @string name
		-- @string sub
		-- @treturn boolean
		function Tags:HasSublink (name, sub)
			return FindSublink(self, name, sub) ~= nil
		end
	end

	do
		--
		local function AuxIs (T, name, super)
			for _, tname in Parents(T, name) do
				if tname == super or AuxIs(T, tname, super) then
					return true
				end
			end

			return false
		end

		--- DOCME
		-- @string name
		-- @string what
		-- @treturn boolean
		function Tags:Is (name, what)
			return name == what or AuxIs(self, name, what)
		end
	end

	do
		-- Iterator body
		local function AuxParents (tag, i)
			return Name(tag, i - 1)
		end

		--- Iterator.
		-- @string name Tag name.
		-- @treturn iterator Supplies, in order, at each iteration:
		--
		-- * Iteration variable, of dubious practical use.
		-- * Parent tag name, as assigned in @{Tags:New} for _name_. (Grandparents, et al. are
		-- **not** iterated.)
		function Tags:Parents (name)
			local tag = self[_tags][name]

			return AuxParents, tag, tag and tag.nparents + 1 or 0
		end
	end

	-- --
	local function NoOp () end

	--
	local function Pairs (t)
		if t then
			return pairs(t)
		else
			return NoOp
		end
	end

	do
		-- Sublink class definition --
		local Sublink = class.Define(function(Sublink)
			--- DOCME
			function Sublink:GetName ()
				return self[_name]
			end

			--- DOCME
			function Sublink:Implements (what)
				return adaptive.InSet(self[_interfaces], what)
			end

			--- DOCME
			function Sublink:__cons (name)
				self[_name] = name
			end
		end)

		--
		local function AddInterface (sub, what)
			adaptive.AddToSet(sub, _interfaces, what)
		end

		--
		local function LinkToAny () return true end

		--
		local function CanLinkTo (_, _, sub, other_sub)
			if other_sub:Implements(sub[_link_to]) then
				return true
			else
				return false, "Expected `" .. sub[_link_to] .. "`", true
			end
		end

		--- DOCME
		function Tags:ImpliesInterface (name, what)
			adaptive.AddToSet(self[_implies], name, what)
		end

		--- DOCME
		function Tags:Implementors (what)
			return TagAndChildren(self, self[_implemented_by][what], true)
		end

		--
		local function AddImplementor (T, name, what)
			local implemented_by = T[_implemented_by]

			for impl_by in adaptive.IterSet(implemented_by[what]) do
				if Is(T, name, impl_by) then
					return
				end
			end

			adaptive.AddToSet(implemented_by, what, name)
		end

		--- DOCME
		-- @string name
		-- @ptable options
		function Tags:New (name, options)
			local tags = self[_tags]

			assert(not tags[name], "Tag already exists")

			local tag, new = {}

			if options then
				-- We track the tag's parent and child tag names, so that these may be iterated.
				-- The parents are only assigned at tag creation, so we can safely put these at
				-- the beginning of the tag's info array; whereas child tags may be added over
				-- time. By making note of how many parents there were, however, we can append
				-- the children to the same array: namely, the new tag name itself is here added
				-- to each of its parents.
				for _, pname in ipairs(options) do
					local ptag = assert(tags[pname], "Invalid parent")

					assert(ptag[#ptag] ~= name, "Duplicate parent")

					ptag[#ptag + 1], tag[#tag + 1] = name, pname
				end

				-- Add any sublinks.
				local sub_links, implies = options.sub_links, self[_implies]

				if sub_links then
					new = {}

					for name, sub in pairs(sub_links) do
						local stype, obj, link_to = type(sub), Sublink(name)

						--
						if stype == "table" then
							for _, v in ipairs(sub) do
								AddInterface(obj, v)
							end

							--
							link_to = sub.link_to

						--
						elseif sub then
							link_to = sub ~= true and sub
						end
						
						--
						if type(link_to) == "string" then
							obj[_can_link], obj[_link_to] = CanLinkTo, link_to

							--
							for interface in adaptive.IterSet(implies[link_to]) do
								AddInterface(obj, interface)
							end

						--
						elseif link_to ~= nil then
							obj[_can_link] = link_to or LinkToAny
						end

						--
						new[name] = obj
					end
				end

				--
				for _, sub in Pairs(new) do
					for what in adaptive.IterSet(sub[_interfaces]) do
						AddImplementor(self, name, what)
					end
				end

				-- Record anything else that could be a property.
				for k, v in pairs(options) do
					tag[k] = v
				end
			end

			--
			tag.nparents, tag.sub_links = #(options or ""), new

			tags[name] = tag
		end
	end

	do
		-- Enumerator body
		local function EnumSublinks (T, str_list, name, count)
			for _, tname in Parents(T, name) do
				count = EnumSublinks(T, str_list, tname, count)
			end

			--
			for _, v in Pairs(Tags[name].sub_links) do
				str_list[count + 1], count = v:GetName(), count + 1
			end

			return count
		end

		--- DOCME
		-- @string name
		-- @treturn iterator I
		function Tags:Sublinks (name)
			return IterStrList(self, EnumSublinks, name)
		end
	end

	do
		-- Enumerator body
		local function EnumTagAndChildren (T, str_list, name, count)
			for _, tname in Children(T, name) do
				count = EnumTagAndChildren(T, str_list, tname, count)
			end

			str_list[count + 1] = name

			return count + 1
		end

		--- DOCME
		-- @string name
		-- @bool as_set
		-- @treturn iterator I
		function Tags:TagAndChildren (name, as_set)
			return IterStrList(self, EnumTagAndChildren, name, as_set)
		end
	end

	do
		-- Enumerator body
		local function EnumTagAndParents (T, str_list, name, count)
			for _, tname in Parents(T, name) do
				count = EnumTagAndParents(T, str_list, tname, count)
			end

			str_list[count + 1] = name

			return count + 1
		end

		--- Iterator.
		-- @string name Tag name.
		-- @bool as_set
		-- @treturn iterator Supplies, in some order without duplication, at each iteration:
		--
		-- * Iteration variable, of dubious practical use.
		-- * Tag name, which may be _name_ itself; a parent tag name, as assigned in @{Tags:New} for
		-- _name_; the parent tag name, in turn, of such a parent, etc.
		function Tags:TagAndParents (name, as_set)
			return IterStrList(self, EnumTagAndParents, name, as_set)
		end
	end

	do
		-- Enumerator body
		local function EnumTags (T, str_list, _, count)
			for k in pairs(T[_tags]) do
				str_list[count + 1], count = k, count + 1
			end

			return count
		end

		--- Iterator.
		-- @treturn iterator Supplies, in some order without duplication, at each iteration:
		--
		-- * Iteration variable, of dubious practical use.
		-- * Tag name, as assigned in @{Tags:New}.
		function Tags:Tags ()
			return IterStrList(self, EnumTags, true)
		end
	end

	--- Class constructor.
	function Tags:__cons ()
		self[_implemented_by] = {}
		self[_implies] = {}
		self[_tags] = {}
	end

	-- Bind references.
	Children, Is, Parents, TagAndChildren = Tags.Children, Tags.Is, Tags.Parents, Tags.TagAndChildren
end)