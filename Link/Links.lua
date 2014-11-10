--- Object linking components.

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
local min = math.min
local next = next
local pairs = pairs
local type = type
local yield = coroutine.yield

-- Modules --
local array_funcs = require("tektite_core.array.funcs")
local class = require("tektite_core.class")
local coro = require("iterator_ops.coroutine")
local strings = require("tektite_core.var.strings")

-- Classes --
local SparseArray = require("tektite_base_classes.Container.StableArray")
local Tags = require("tektite_base_classes.Link.Tags")

-- Unique member keys (Links) --
local _alive = {}
local _links = {}
local _objects = {}
local _on_assign = {}
local _on_remove = {}
local _proxies = {}
local _tagged_lists = {}
local _tags = {}

-- Unique member keys (Link) --
local _on_break = {}
local _parent = {}
local _proxy1 = {}
local _proxy2 = {}
local _sub1 = {}
local _sub2 = {}

-- --
local function NoOp () end

--
local function NumberPairs (t, k)
	repeat
		k = next(t, k)
	until k == nil or type(k) == "number"

	return k, t[k]
end

-- Helper to visit a proxy's link keys
local function LinkKeys (proxy)
	if proxy then
		return NumberPairs, proxy
	else
		return NoOp
	end
end

-- Gets the key for a proxy pairing
local function GetKey (p1, p2)
	return p1[p2.id]
end

--
local function LinksIter (L, p1, p2)
	local key = GetKey(p1, p2)
	local t = key and L[_links][key]

	if t then
		return ipairs(t)
	else
		return NoOp
	end
end

--
local function SetInTaggedList (L, name, id, proxy)
	local tagged_lists = L[_tagged_lists]
	local list = tagged_lists[name]

	if list or proxy then
		list = list or {}

		list[id], tagged_lists[name] = proxy, list
	end
end

--
local function RemoveObject (L, id, object)
	local links, proxies = L[_links], L[_proxies]

	--
	local proxy = proxies[object]

	proxies[object], proxy.id = nil

	for _, v in LinkKeys(proxy) do
		for _, link in pairs(links[v]) do
			link:Break()
		end
	end

	--
	SetInTaggedList(L, proxy.name, id, nil)

	--
	local on_remove = L[_on_remove]

	if on_remove then
		on_remove(object)
	end

	L[_objects]:RemoveAt(id)
end

-- Helper to get an object (if valid) from a proxy
-- If the object has gone dead, it is removed, and considered to be nil
local function Object (L, proxy)
	local id = proxy and proxy.id

	if id then
		local object = L[_objects]:Get(id)

		if L[_alive](object) then
			return object
		else
			RemoveObject(L, id, object)
		end
	end

	return nil
end

-- --
local LinksClass

-- Link class definition --
local SingleLink = class.Define(function(Link)
	-- Helper to find a link for a proxy pair
	local function FindLink (parent, p1, p2, link)
		for i, v in LinksIter(parent, p1, p2) do
			if v == link then
				return i
			end
		end
	end

	--- Breaks this line, after which it will be invalid.
	--
	-- If the link is already invalid, this is a no-op.
	-- @see Link:IsValid
	function Link:Break ()
		local p1, p2 = self[_proxy1], self[_proxy2]

		-- With the proxies now safely cached (if still present), clear the proxy fields to abort
		-- recursion (namely, in case of dead objects).
		self[_proxy1], self[_proxy2] = nil

		-- If the objects were both valid, the link is still intact. In this case, remove it from
		-- the pair's list; if this empties the list, remove that as well, from both the master
		-- list and each proxy.
		local parent = self[_parent]
		local obj1 = Object(parent, p1)
		local obj2 = Object(parent, p2)

		if obj1 and obj2 then
			local key, plinks = GetKey(p1, p2), parent[_links]
			local links = plinks[key]

			array_funcs.Backfill(links, FindLink(parent, p1, p2, self))

			if #links == 0 then
				plinks[key], p1[p2.id], p2[p1.id] = nil
			end
		end

		-- If this link went from intact to broken, call any handler.
		local on_break = p1 and self[_on_break]

		if on_break then
			on_break(self, obj1, obj2, self[_sub1], self[_sub2])
		end
	end

	--- Getter.
	-- @treturn boolean The link is still intact?
	--
	-- When **false**, this is the only return value.
	-- @treturn ?pobject Linked object #1...
	-- @treturn ?pobject ...and #2.
	-- @treturn ?string Sublink of object #1...
	-- @treturn ?string ...and object #2.
	-- @see Link:IsValid
	function Link:GetObjects ()
		local parent = self[_parent]
		local obj1, obj2 = Object(parent, self[_proxy1]), Object(parent, self[_proxy2])

		if obj1 and obj2 then
			return true, obj1, obj2, self[_sub1], self[_sub2]
		end

		return false
	end

	--- Getter.
	-- @pobject object Object, which may be paired in the link.
	-- @treturn ?pobject If the link is valid and _object_ was one of its linked objects, the
	-- other object; otherwise, **nil**.
	-- @treturn ?string If an object was returned, its sublink; if absent, **nil**.
	function Link:GetOtherObject (object)
		local _, obj1, obj2, sub1, sub2 = self:GetObjects()

		if obj1 == object then
			return obj2, sub2
		elseif obj2 == object then
			return obj1, sub1
		end

		return nil
	end

	--- Checks link validity. Links are invalid after @{Link:Break}, or if one or both of
	-- the proxied objects has been removed.
	-- @treturn boolean The link is still intact?
	function Link:IsValid ()
		local parent = self[_parent]

		return (Object(parent, self[_proxy1]) and Object(parent, self[_proxy2])) ~= nil
	end

	--- Sets logic to call when a link becomes invalid, cf. @{Link:IsValid}.
	--
	-- Called as
	--    func(link, object1, object2, sub1, sub2)
	-- where _object1_ and _object2_ were the linked objects and _sub1_ and _sub2_ were their
	-- respective sublinks. In the case that _object*_ has been removed, it will be **nil**.
	--
	-- **N.B.** This may be triggered lazily, i.e. outside of @{Link:Break}, either via one of
	-- the other link methods or @{Links:CleanUp}.
	-- @callable func Function to assign, or **nil** to disable the logic.
	function Link:SetBreakFunc (func)
		self[_on_break] = func
	end

	--- Class constructor.
	-- DOCMEMORE
	function Link:__cons (parent, proxy1, proxy2, sub1, sub2)
		assert(class.Type(parent) == LinksClass, "Non-links parent")

		self[_parent] = parent
		self[_proxy1] = proxy1
		self[_proxy2] = proxy2
		self[_sub1] = sub1
		self[_sub2] = sub2
	end
end)

-- Links class definition --
LinksClass = class.Define(function(Links)
	-- Helper to clean up any dead objects in a range
	local function AuxCleanUp (L, from, to)
		local alive, objects = L[_alive], L[_objects]

		for i = from, to do
			if objects:InUse(i) then
				local object = objects:Get(i)

				if not alive(object) then
					RemoveObject(L, i, object)
				end
			end
		end
	end

	--- Visits a range of objects, performing cleanup on any that have been removed.
	--
	-- Cleanup of an object consists in breaking any links it has made, invalidating its proxy,
	-- and removing it from its tag's list.
	-- @uint from ID of first (possible) object.
	-- @uint count Number of objects to check.
	-- @treturn uint First ID after visited objects.
	function Links:CleanUp (from, count)
		local nobjs = #self[_objects]
		local to = from + min(count, nobjs) - 1

		AuxCleanUp(self, from, min(to, nobjs))

		if to >= nobjs then
			to = to - nobjs

			AuxCleanUp(self, 1, to)
		end

		return to + 1
	end

	--
	local function Match1 (link, proxy, sub)
		return link[_proxy1] == proxy and link[_sub1] == sub
	end

	--
	local function Match2 (link, proxy, sub)
		return link[_proxy2] == proxy and link[_sub2] == sub
	end

	-- Helper to get a proxy (if valid) from an object
	local function Proxy (L, object)
		return object and L[_alive](object) and L[_proxies][object]
	end

	--- Getter.
	-- @pobject object
	-- @string sub
	-- @treturn uint C
	function Links:CountLinks (object, sub)
		local proxy, links, count = Proxy(self, object), self[_links], 0

		for _, v in LinkKeys(proxy) do
			for _, link in pairs(links[v]) do
				if Match1(link, proxy, sub) or Match2(link, proxy, sub) then
					count = count + 1
				end
			end
		end

		return count
	end

	--
	local function AlreadyLinked (L, p1, p2, sub1, sub2)
		for _, link in LinksIter(L, p1, p2) do
			if Match1(link, p1, sub1) and Match2(link, p2, sub2) then
				return true
			end
		end
	end

	--
	local function SortProxies (p1, p2, sub1, sub2, obj1, obj2)
		if p2.id < p1.id then
			return p2, p1, sub2, sub1, obj2, obj1
		else
			return p1, p2, sub1, sub2, obj1, obj2
		end
	end

	--- DOCME
	-- @pobject object1
	-- @pobject object2
	-- @string sub1
	-- @string sub2
	-- @treturn boolean X If true, this is the only return value.
	-- @treturn ?string Reason link cannot be formed.
	-- @treturn ?boolean This is a contradiction or "strong" failure, i.e. the predicate will
	-- **always** fail, given the inputs?
	function Links:CanLink (object1, object2, sub1, sub2)
		local p1, p2 = Proxy(self, object1), Proxy(self, object2)

		-- Both objects are still valid?
		if p1 and p2 then
			p1, p2, sub1, sub2, object1, object2 = SortProxies(p1, p2, sub1, sub2, object1, object2)

			if p1 == p2 or AlreadyLinked(self, p1, p2, sub1, sub2) then
				return false, p1 == p2 and "Same object" or "Already linked"

			-- ...and not already linked?
			else
				local tags = self[_tags]

				-- ...pass all object1-object2 predicates?
				local passed, why, is_cont = tags:CanLink(p1.name, p2.name, object1, object2, sub1, sub2)

				if passed then
					-- ...and object2-object1 ones too?
					passed, why, is_cont = tags:CanLink(p2.name, p1.name, object2, object1, sub2, sub1)

					if passed then
						return true
					end
				end

				return false, why, is_cont
			end
		end

		return false, "Invalid object", true
	end

	--- Getter.
	-- @pobject object
	-- @bool is_proxy
	-- @treturn string N
	function Links:GetTag (object, is_proxy)
		if not is_proxy then
			object = Proxy(self, object)
		end

		return object and object.name
	end

	--- Predicate.
	-- @pobject object
	-- @string sub
	-- @treturn boolean X
	function Links:HasLinks (object, sub)
		local proxy, links = Proxy(self, object), self[_links]

		for _, v in LinkKeys(proxy) do
			for _, link in pairs(links[v]) do
				if Match1(link, proxy, sub) or Match2(link, proxy, sub) then
					return true
				end
			end
		end

		return false
	end

	--- DOCME
	-- @pobject object1
	-- @pobject object2
	-- @string sub1
	-- @string sub2
	-- @treturn LinkHandle L
	-- @treturn string S
	-- @treturn boolean B
	function Links:LinkObjects (object1, object2, sub1, sub2)
		local can_link, why, is_cont = self:CanLink(object1, object2, sub1, sub2) 

		if can_link then
			local proxies, p1, p2 = self[_proxies]

			-- To limit a few checks later on, impose an order on the proxies.
			p1, p2, sub1, sub2 = SortProxies(proxies[object1], proxies[object2], sub1, sub2)

			-- Lookup the links already associated with this pairing. If this is the first,
			-- generate the key and list and hook everything up.
			local key, links = GetKey(p1, p2), self[_links]
			local klinks = links[key]

			if not key then
				key, klinks = strings.PairToKey(p1.id, p2.id), {}

				links[key], p1[p2.id], p2[p1.id] = links, key, key
			end

			-- Install the link.
			local link = SingleLink(self, p1, p2, sub1, sub2)

			klinks[#klinks + 1] = link

			return link
		end

		return nil, why, is_cont
	end

	--- DOCME
	-- @function Links:Links
	-- @pobject object
	-- @string sub
	-- @treturn iterator X
	Links.Links = coro.Iterator(function(L, object, sub)
		local proxy, links = Proxy(L, object), L[_links]

		for _, v in LinkKeys(proxy) do
			for _, link in pairs(links[v]) do
				if Match1(link, proxy, sub) or Match2(link, proxy, sub) then
					yield(link)
				end
			end
		end
	end)

	--- DOCME
	-- @pobject object
	function Links:RemoveTag (object)
		local proxy = Proxy(self, object)

		if proxy then
			RemoveObject(self, proxy.id, object)
		end
	end

	--- Setter.
	-- @callable func X
	function Links:SetAssignFunc (func)
		self[_on_assign] = func
	end

	--- Setter.
	-- @callable func X
	function Links:SetRemoveFunc (func)
		self[_on_remove] = func
	end

	--- DOCME
	-- @pobject object
	-- @string name
	function Links:SetTag (object, name)
		assert(object and self[_alive](object), "Invalid object")

		local proxies = self[_proxies]

		assert(not proxies[object], "Object already tagged")

		local proxy = { id = self[_objects]:Insert(object), name = name }

		proxies[object] = proxy

		--
		SetInTaggedList(self, name, proxy.id, proxy)

		--
		local on_assign = self[_on_assign]

		if on_assign then
			on_assign(object)
		end
		--[[
				-- There may be many objects, so deal with just a slice at a time.
				else
					index = M.CleanUp(index, 15)
				end
			^^ ??????
		]]
	end

	--- DOCME
	-- @function Links:Tagged
	-- @string name N
	-- @treturn iterator X
	Links.Tagged = coro.Iterator(function(L, name)
		local list = L[_tagged_lists][name]

		if list then
			for _, proxy in pairs(list) do
				local object = Object(L, proxy)

				if object then
					yield(object)
				end
			end
		end
	end)

	--- Class constructor.
	function Links:__cons (tags, alive)
		assert(class.Type(tags) == Tags, "Non-tags argument")

		self[_alive] = alive
		self[_objects] = SparseArray()
		self[_links] = {}
		self[_proxies] = {}
		self[_tagged_lists] = {}
		self[_tags] = tags
	end
end)

return LinksClass