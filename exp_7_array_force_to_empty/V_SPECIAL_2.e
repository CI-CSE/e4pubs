note
    description: "Wrapper around SPECIAL for use in verification."
	author: "Nadia Polikarpova"
	revised_by: "Alexander Kogtenkov"
	model: sequence, capacity
	manual_inv: true
	false_guards: true

class
	V_SPECIAL_2 [T]

create
	make_empty,
	make_filled

feature {NONE} -- Initialization

	make_empty (n: INTEGER)
			-- Create a special object for `n' entries.
		note
			status: creator
		require
			non_negative_argument: n >= 0
		do
			capacity := n
		ensure
			sequence_effect: sequence.is_empty
			capacity_effect: capacity = n
		end

	make_filled (v: T; n: INTEGER)
			-- Create a special object for `n' entries initialized with `v'.
		note
			status: creator
			explicit: wrapping
		require
			non_negative_argument: n >= 0
		do
			make_empty (n)
			fill_with (v, 0, n - 1)
		ensure
			sequence_domain_effect: sequence.count = n
			sequence_effect: across 1 |..| sequence.count as i all sequence [i] = v end
			capacity_effect: capacity = n
			is_wrapped
		end

feature -- Access

	item alias "[]" (i: INTEGER): T assign put
			-- Item at `i'-th position
			-- (indices begin at 0)
		require
			valid_index: valid_index (i)
		do
			Result := sequence [i + 1]
		ensure
			definition: Result = sequence [i + 1]
		end

feature -- Measurement

	count: INTEGER
			-- Count of special area
		do
			Result := sequence.count
		ensure
			definition: Result = sequence.count
		end

	capacity: INTEGER
			-- Capacity of special area

feature -- Status report

	valid_index (i: INTEGER): BOOLEAN
			-- Is `i' within the bounds of Current?
		do
			Result := (0 <= i) and (i < count)
		ensure
			definition: Result = (0 <= i and i < sequence.count)
		end

	same_items (other: like Current; source_index, destination_index, n: INTEGER): BOOLEAN
			-- Are the `n' elements of `other' from `source_index' position the same as
			-- the `n' elements of `Current' from `destination_index'?
			-- (Use reference equality for comparison.)
		require
			other_not_void: other /= Void
			source_index_non_negative: source_index >= 0
			destination_index_non_negative: destination_index >= 0
			n_non_negative: n >= 0
			n_is_small_enough_for_source: source_index + n <= other.count
			n_is_small_enough_for_destination: destination_index + n <= count
		local
			i, j, nb: INTEGER
		do
			Result := True
			if other /= Current or source_index /= destination_index then
				from
					i := source_index
					j := destination_index
					nb := source_index + n
				invariant
					source_index <= i and i <= source_index + n
					destination_index <= j and j <= destination_index + n
					i - source_index = j - destination_index
					Result implies (across (source_index + 1) |..| i as k all other.sequence [k] = sequence [destination_index - source_index + k] end)
					not Result implies source_index + 1 <= i and other.sequence [i] /= sequence [j]
				until
					i = nb or not Result
				loop
					if other.item (i) /= item (j) then
						Result := False
					end
					i := i + 1
					j := j + 1
				variant
					nb - i
				end
			end
		ensure
			definition: Result =
					across (source_index + 1) |..| (source_index + n) as k all other.sequence [k] = sequence [destination_index - source_index + k] end
		end

feature -- Element change

	put (v: T; i: INTEGER)
			-- Replace `i'-th item by `v'.
			-- (Indices begin at 0.)
		require
			index_large_enough: i >= 0
			index_small_enough: i < count
		do
			sequence := sequence.replaced_at (i + 1, v)
		ensure
			sequence_effect: sequence ~ old sequence.replaced_at (i + 1, v)
			modify_model ("sequence", Current)
		end

	extend (v: T)
			-- Add `v' at index `count'.
		require
			count_small_enough: count < capacity
		do
			sequence := sequence & v
		ensure
			sequence_effect: sequence ~ old sequence & v
			modify_model ("sequence", Current)
		end

	fill_with (v: T; start_index, end_index: INTEGER)
			-- Set items between `start_index' and `end_index' with `v'.
		note
			explicit: wrapping
		require
			start_index_non_negative: start_index >= 0
			start_index_in_bound: start_index <= count
			start_index_not_too_big: start_index <= end_index + 1
			end_index_valid: end_index < capacity
		local
			i, nb: INTEGER
			l_count: like count
		do
			from
				i := start_index
				l_count := count.min (end_index + 1)
				nb := l_count
			invariant
				is_wrapped
				l_count = sequence.count.old_.min (end_index + 1)
				sequence.count = sequence.count.old_
				nb = l_count
				start_index <= i and i <= nb
				across (start_index + 1) |..| i as k all sequence [k] = v end
				across 1 |..| start_index as k all sequence [k] = sequence.old_ [k] end
				across (end_index + 2) |..| sequence.count as k all sequence [k] = sequence.old_ [k] end
			until
				i = nb
			loop
				put (v, i)
				i := i + 1
			end
			from
				i := l_count
				nb := end_index + 1
			invariant
				is_wrapped
				nb = end_index + 1
				l_count <= i and i <= nb
				sequence.count = if sequence.count.old_ < end_index + 1 then i else sequence.count.old_ end
				across (start_index + 1) |..| i as k all sequence [k] = v end
				across 1 |..| start_index as k all sequence [k] = sequence.old_ [k] end
				across (end_index + 2) |..| sequence.count as k all sequence [k] = sequence.old_ [k] end
			until
				i = nb
			loop
				extend (v)
				i := i + 1
			end
		ensure
			sequence_domain_effect: sequence.count = (old sequence.count).max (end_index + 1)
			sequence_effect: across (start_index + 1) |..| (end_index + 1) as k all sequence [k] = v end
			sequence_front_unchanged: across 1 |..| start_index as k all sequence [k] = (old sequence) [k] end
			sequence_tail_unchanged: across (end_index + 2) |..| sequence.count as k all sequence [k] = (old sequence) [k] end
			modify_model ("sequence", Current)
		end

	fill_with_default (start_index, end_index: INTEGER)
			-- Clear items between `start_index' and `end_index'.
		note
			explicit: wrapping
		require
--			is_self_initializing: ({T}).has_default
			start_index_non_negative: start_index >= 0
			start_index_not_too_big: start_index <= end_index + 1
			end_index_valid: end_index < count
		do
			check inv end
			fill_with (({T}).default, start_index, end_index)
		ensure
			sequence_domain_effect: sequence.count = old sequence.count
			sequence_effect: across (start_index + 1) |..| (end_index + 1) as k all sequence [k] = ({T}).default end
			sequence_front_unchanged: across 1 |..| start_index as k all sequence [k] = (old sequence) [k] end
			sequence_tail_unchanged: across (end_index + 2) |..| sequence.count as k all sequence [k] = (old sequence) [k] end
			modify_model ("sequence", Current)
		end

	copy_data (other: V_SPECIAL_2 [T]; source_index, destination_index, n: INTEGER)
			-- Copy `n' elements of `other' from `source_index' position to Current at
			-- `destination_index'. Other elements of Current remain unchanged.
		note
			explicit: contracts
		require
			wrapped: is_wrapped
			other_not_void: other /= Void
			source_index_non_negative: source_index >= 0
			destination_index_non_negative: destination_index >= 0
			destination_index_in_bound: destination_index <= count
			n_non_negative: n >= 0
			n_is_small_enough_for_source: source_index + n <= other.count
			n_is_small_enough_for_destination: destination_index + n <= capacity
--			same_type: other.conforms_to (Current)
		do
				-- ToDo
			sequence := sequence.front (destination_index) +
				other.sequence.interval (source_index + 1, source_index + n) +
				sequence.tail (destination_index + n + 1)
		ensure
			sequence_effect: sequence ~ old (
							sequence.front (destination_index) +
							other.sequence.interval (source_index + 1, source_index + n) +
							sequence.tail (destination_index + n + 1))
			wrapped: is_wrapped
			modify_model ("sequence", Current)
		end

feature -- Resizing


	aliased_resized_area (n: INTEGER): like Current
			-- Try to resize `Current' with a count of `n', if not
			-- possible a new copy
		note
			status: impure
		require
			n_non_negative: n >= 0
		do
			unwrap
			capacity := n
			sequence := sequence.front (n)
			wrap
			Result := Current
		ensure
			result_wrapped: Result.is_wrapped
			current_or_fresh: Result = Current or Result.is_fresh
			capacity_definition: Result.capacity = n
			sequence_definition: Result.sequence ~ old sequence.front (n)
			modify (Current)
		end

feature -- Specification

	sequence: MML_SEQUENCE [T]
			-- Sequence of elements
		note
			status: ghost
		attribute
			check is_executable: False then end
		end

invariant
	capacity_constraint: sequence.count <= capacity

note
	copyright: "Copyright (c) 1984-2021, Eiffel Software and others"
	license: "Eiffel Forum License v2 (see http://www.eiffel.com/licensing/forum.txt)"
	source: "[
			Eiffel Software
			5949 Hollister Ave., Goleta, CA 93117 USA
			Telephone 805-685-1006, Fax 805-685-6869
			Website http://www.eiffel.com
			Customer support http://support.eiffel.com
		]"

end
