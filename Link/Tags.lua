--- This class provides a way to label a set of types, suggest any general behaviors they
-- implement, and describe what connections are allowed among them, horizontally as well
-- as hierarchically.
-- @module Tags

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
local setmetatable = setmetatable
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
local _template = {}

-- Unique member keys (Tags) --
local _implemented_by = {}
local _implies = {}
local _tags = {}

-- Iterator over a list of strings (tags or sublinks)
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
		-- Build up the list of strings, accommodating the form of the source.
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
		local function AuxHasSublink (T, name, sub, arg)
			--
			local tag = T[_tags][name]
			local sub_links = tag.sub_links

			if sub_links then
				local sublink = sub_links[sub]

				if sublink then
					return sublink
				elseif arg == "template" then
					local templates = tag.templates

					return templates and templates[sub]
				elseif arg then
					local instances = tag.instances
					local object_list = instances and instances[arg]

					return object_list and object_list[sub]
				end
			end

			--
			for _, tname in Parents(T, name) do
				local sublink = AuxHasSublink(T, tname, sub, arg)

				if sublink then
					return sublink
				end
			end
		end

		-- --
		local Name1, Sub1, Sublink1
		local Name2, Sub2, Sublink2

		--
		local function FindSublink (T, name, sub, arg)
			if name == Name1 and sub == Sub1 then
				return Sublink1
			elseif name == Name2 and sub == Sub2 then
				return Sublink2
			else
				local sublink = AuxHasSublink(T, name, sub, arg)

				Name1, Sub1, Sublink1 = name, sub, sublink
				Name2, Sub2, Sublink2 = Name1, Sub1, Sublink1

				return sublink
			end
		end

		--- DOCME
		function Tags:CanLink (name1, name2, object1, object2, sub1, sub2, arg)
			local so1, is_cont, passed, why = FindSublink(self, name1, sub1, object1), true

			if so1 then
				local so2 = FindSublink(self, name2, sub2, object2)

				if so2 then
					passed, why, is_cont = so1[_can_link](object1, object2, so1, so2, arg)
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
		-- @param[opt] arg
		-- @treturn boolean
		function Tags:HasSublink (name, sub, arg)
			return FindSublink(self, name, sub, arg) ~= nil
		end

		--- Predicate.
		-- @param name
		-- @string sub
		-- @param what
		-- @param[opt] arg
		-- @treturn boolean X
		function Tags:ImplementedBySublink (name, sub, what, arg)
			local sub_link = FindSublink(self, name, sub, arg)

			return sub_link ~= nil and sub_link:Implements(what)
		end

		--- DOCME
		-- @string name
		-- @string sub
		-- @param object
		-- @treturn ?|string|nil X
		function Tags:Instantiate (name, sub, object)
			local template, instance = FindSublink(self, name, sub, "template")

			if template then
				local tag, new = self[_tags][name], template:Clone()
				local object_list = tag.instances[object] or { id = 0 }
				local id = object_list.id + 1

				instance = ("%s:%i"):format(sub, id)
					
				tag.instances[object], object_list[instance], object_list.id = object_list, new, id
			end

			return instance
		end

		--- DOCME
		-- @string name
		-- @string sub
		-- @param object
		-- @treturn boolean X
		function Tags:Release (name, instance, object)
			local exists = FindSublink(self, name, instance, object) ~= nil

			if exists then
				self[_tags][name].instances[object][instance] = nil
			end

			return exists
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

	-- Nothing to iterate
	local function NoOp () end

	-- Iterate pairs()-style, if the table exists
	local function Pairs (t)
		if t then
			return pairs(t)
		else
			return NoOp
		end
	end

	do
		-- Sublink class definition --
		local SublinkClass = class.Define(function(Sublink)
			--- Getter.
			-- @treturn string Sublink name.
			function Sublink:GetName ()
				return self[_name]
			end

			--- Predicate.
			-- @param what
			-- @treturn boolean X
			function Sublink:Implements (what)
				return adaptive.InSet((self[_template] or self)[_interfaces], what)
			end

			--- Class cloner.
			function Sublink:__clone (S)
				self[_name], self[_template] = S[_name], S
			end

			--- Class constructor.
			-- @string name Sublink name.
			function Sublink:__cons (name)
				self[_name] = name
			end
		end)

		--- DOCME
		function Tags:GetTemplate (name, instance, object)
			local instances = self[_tags][name].instances
			local object_list = instances and instances[object]
			local sublink = object_list and object_list[instance]

			return sublink and sublink[_template]:GetName()
		end
			
		--
		local function AddInterface (sub, what)
			adaptive.AddToSet_Member(sub, _interfaces, what)
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
		-- @treturn iterator I
		function Tags:Implementors (what)
			return TagAndChildren(self, self[_implemented_by][what], true)
		end

		--- DOCME
		-- @param name
		-- @param what
		function Tags:ImplyInterface (name, what)
			adaptive.AddToSet_Member(self[_implies], name, what)
		end

		--
		local function AddImplementor (T, name, what)
			local implemented_by = T[_implemented_by]

			for impl_by in adaptive.IterSet(implemented_by[what]) do
				if Is(T, name, impl_by) then
					return
				end
			end

			adaptive.AddToSet_Member(implemented_by, what, name)
		end

		-- --
		local ObjectListMT = { __mode = "k" }

		--- DOCME
		-- @string name
		-- @ptable[opt] options
		function Tags:New (name, options)
			local tags = self[_tags]

			assert(not tags[name], "Tag already exists")

			local tag, new, tlist = {}

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
				local sub_links, templates, implies = options.sub_links, options.templates, self[_implies]

				if sub_links then
					new = {}

					for name, sub in pairs(sub_links) do
						local stype, obj, link_to = type(sub), SublinkClass(name)

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
						if templates and templates[name] then
							tlist = tlist or {}
							tlist[name] = obj
						else
							new[name] = obj
						end
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
			tag.nparents, tag.sub_links, tag.templates = #(options or ""), new, tlist

			if tlist then
				tag.instances = setmetatable({}, ObjectListMT)
			end

			tags[name] = tag
		end
	end

	do
		-- TODO: instances (generalize MakeEnumerator / IterStrList?)

		-- Enumerator body
		local function MakeEnumerator (key)
			local function enum (T, str_list, name, count)
				for _, tname in Parents(T, name) do
					count = enum(T, str_list, tname, count)
				end

				--
				for _, v in Pairs(T[_tags][name][key]) do
					str_list[count + 1], count = v:GetName(), count + 1
				end

				return count
			end

			return enum
		end

		--
		local EnumSublinks = MakeEnumerator("sub_links")

		--- DOCME
		-- @string name
		-- @treturn iterator I
		function Tags:Sublinks (name)
			return IterStrList(self, EnumSublinks, name)
		end

		--
		local EnumTemplates = MakeEnumerator("templates")

		--- DOCME
		-- @string name
		-- @treturn iterator I
		function Tags:Templates (name)
			return IterStrList(self, EnumTemplates, name)
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