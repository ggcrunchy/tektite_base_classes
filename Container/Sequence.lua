--- An instance of this class wraps a user-provided 
-- @module Sequence

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
local insert = table.insert
local ipairs = ipairs
local pairs = pairs

-- Modules --
local class = require("tektite_core.class")
local index_funcs = require("tektite_core.array.index")
local var_preds = require("tektite_core.var.predicates")

-- Imports --
local IndexInRange = index_funcs.IndexInRange
local IsCallable = var_preds.IsCallable
local IsCountable = var_preds.IsCountable
local IsType = class.IsType
local RangeOverlap = index_funcs.RangeOverlap

-- Unique member keys (General) --
local _size = {}

-- Unique member keys (Interval) --
local _count = {}
local _start = {}

-- Unique member keys (Sequence) --
local _insert = {}
local _intervals = {}
local _object = {}
local _remove = {}
local _spots = {}

-- Unique member keys (Spot) --
local _can_migrate = {}
local _index = {}
local _is_add_spot = {}

-- Helper tables for iterating operations over monitor objects --
local InsertOps, RemoveOps = {}, {}

-- Interval class definition --
local IntervalClass = class.Define(function(Interval)
	--- Clears the selection.
	function Interval:Clear ()
		self[_count] = 0
	end

	--- Gets the starting position of the interval.
	-- @treturn ?uint Current start index, or **nil** if empty.
	function Interval:GetStart ()
		return self[_count] > 0 and self[_start] or nil
	end

	--- Metamethod.
	-- @treturn uint Size of selected interval.
	function Interval:__len ()
		return self[_count]
	end

	--- Selects a range. The selection count is clamped against the sequence size.
	-- @uint start Current index of start position.
	-- @uint count Current size of range to select.
	function Interval:Set (start, count)
		self[_start] = start
		self[_count] = RangeOverlap(start, count, self[_size])
	end

	--- Class constructor.
	-- @tparam Sequence sequence Reference to owner sequence.
	function Interval:__cons (sequence)
		assert(IsType(sequence, "Sequence"), "Invalid sequence")

		-- Current sequence size --
		self[_size] = #sequence

		-- Selection count --
		self[_count] = 0
	end
end)

--
InsertOps[_intervals] = function(I, index, count, new_size)
	I[_start], I[_count] = IntervalAfterInsert(I[_start], I[_count], index, count)
end

--
RemoveOps[_intervals] = function(I, index, count, new_size)
	I[_start], I[_count] = IntervalAfterRemove(I[_start], I[_count], index, count)
end

-- Returns: If true, spot is valid
local function IsValid (S, index)
	return IndexInRange(index, S[_size], S[_is_add_spot])
end

-- Spot class definition --
local SpotClass = class.Define(function(Spot)
	--- Invalidates the spot.
	function Spot:Clear ()
		self[_index] = 0
	end

	--- Gets the current index of the position watched by the spot.
	-- @treturn ?uint Index, or **nil** if the spot is invalid.
	-- @see Spot:Set
	function Spot:GetIndex ()
		local index = self[_index]

		if IsValid(self, index) then
			return index
		end
	end

	--- Assigns the spot a position in the sequence to watch.
	-- @uint index Current position index.
	-- @see Spot:GetIndex
	function Spot:Set (index)
		assert(IsValid(self, index), "Invalid index")

		self[_index] = index
	end

	--- Class constructor.
	-- @tparam Sequence sequence Reference to owner sequence.
	-- @bool is_add_spot This spot can occupy the position immediately after the sequence?
	-- @bool can_migrate This spot can migrate if the part it monitors is removed?
	function Spot:__cons (sequence, is_add_spot, can_migrate)
		assert(IsType(sequence, "Sequence"), "Invalid sequence")

		-- Current sequence size --
		self[_size] = #sequence

		-- Currently referenced sequence element --
		self[_index] = 1

		-- Flags --
		self[_is_add_spot] = not not is_add_spot
		self[_can_migrate] = not not can_migrate
	end
end)

--
InsertOps[_spots] = function(S, index, count, new_size)
	S[_index] = IndexAfterInsert(S[_index], index, count, new_size, S[_is_add_spot])
end

--
RemoveOps[_spots] = function(S, index, count, new_size)
	S[_index] = IndexAfterRemove(S[_index], index, count, new_size, S[_is_add_spot], S[_can_migrate])
end

-- Sequence class definition --
return class.Define(function(Sequence)
	--- DOCME
	function Sequence:AddInterval ()
		local interval = IntervalClass(self)

		insert(self[_intervals], interval)

		return interval
	end

	--- DOCME
	-- @bool is_add_spot This spot can occupy the position immediately after the sequence?
	-- @bool can_migrate This spot can migrate if the part it monitors is removed?
	function Sequence:AddSpot (is_add_spot, can_migrate)
		local spot = SpotClass(self, is_add_spot, can_migrate)

		insert(self[_spots], spot)

		return spot
	end

	--- DOCME
	function Sequence:Append (count, ...)
		--
	end

	-- Element update helper
	local function Update (S, ops, index, count, new_size)
		for k, op in pairs(ops) do
			for _, elem in ipairs(S[k]) do
				op(elem, index, count, new_size)

				elem[_size] = new_size
			end
		end
	end

	-- --
	local In = { _intervals, _spots }

	-- Inserts new items
	-- index: Insertion index
	-- count: Count of items to add
	-- ...: Insertion arguments
	--------------------------------
	function Sequence:Insert (index, count, ...)
		assert(self:IsItemValid(index, true) and count > 0)

		Update(self, InsertOps, index, count, #self + count)

		self[_insert](index, count, ...)
	end

	--- Predicate.
	-- @uint index Index of item in sequence.
	-- @bool is_addable The end of the sequence is valid?
	-- @treturn boolean The item is valid?
	function Sequence:IsItemValid (index, is_addable)
		return IndexInRange(index, #self, is_addable)
	end

	--- Metamethod.
	-- @treturn uint Item count.
	function Sequence:__len ()
		local size = self[_size]

		if size then
			return size(self[_object]) or 0
		else
			return #self[_object]
		end
	end

	-- Removes a series of items
	-- index: Removal index
	-- count: Count of items to remove
	-- ...: Removal arguments
	-- Returns: Count of items removed
	-----------------------------------
	function Sequence:Remove (index, count, ...)
		local cur_size = #self

		count = RangeOverlap(index, count, cur_size)

		if count > 0 then
			Update(self, RemoveOps, index, count, cur_size - count)

			self[_remove](index, count, ...)
		end

		return count
	end

	--- Class constructor.
	-- @param object Sequenced object.
	-- @callable insert Insert routine.
	-- @callable remove Remove routine.
	-- @tparam ?|callable|nil size Optional size routine.
	function Sequence:__cons (object, insert, remove, size)
		assert(IsCallable(size) or (size == nil and IsCountable(object)), "Invalid sequence parameters")

		-- Monitors --
		self[_intervals] = {}
		self[_spots] = {}

		-- Sequenced object --
		self[_object] = object

		-- Sequence operations --
		self[_insert] = insert
		self[_remove] = remove
		self[_size] = size
	end
end)