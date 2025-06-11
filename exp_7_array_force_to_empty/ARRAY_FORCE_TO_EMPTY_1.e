note
    description: "[
			Indexable containers with arbitrary bounds, whose elements are stored in a continuous memory area.
			Random access is constant time, but resizing requires memory reallocation and copying elements, and takes linear time.
			The logical size of array is the same as the physical size of the underlying memory area.
		]"
	author: "Nadia Polikarpova"
	revised_by: "Alexander Kogtenkov"
	model: sequence, lower_
	manual_inv: true
	false_guards: true

frozen class
	ARRAY_FORCE_TO_EMPTY_1 [G]

inherit
	V_MUTABLE_SEQUENCE [G]
		redefine
			is_equal_,
			upper,
			fill,
			clear,
			is_model_equal
		end

create
	make,
	make_filled,
	copy_

feature

	bugged_force_to_empty (v: like item; i: INTEGER)
		require
			observers_open: across observers as o all o.is_open end
			is_empty
		local
			old_size, new_size: INTEGER_32
			new_lower, new_upper: INTEGER_32
			l_count, l_offset: INTEGER_32
			l_increased_by_one: BOOLEAN
		do
			new_lower := lower.min (i)
			new_upper := upper.max (i)
			new_size := new_upper - new_lower + 1
			l_increased_by_one := (i = upper + 1) or (i = lower - 1)
			area := area.aliased_resized_area (new_size)
			if not l_increased_by_one then
				area.fill_with (({G}).default, 0, new_size - 2)
			end
			area.extend (v)
			lower := new_lower
			upper := new_upper
		ensure
			inserted: item (i) = v
			higher_count: count >= old count
			lower_set: lower = (old lower).min (i)
			upper_set: upper = (old upper).max (i)
			sequence_effect: across 1 |..| sequence.count as j all (j = idx (i) and sequence [j] = v) or (j /= idx (i) and sequence [j] = ({G}).default) end
			modify_model (["sequence", "lower_"], Current)
		end

feature {NONE} -- Initialization

	make (l, u: INTEGER)
			-- Create array with indexes in [`l', `u']; set all values to default.
		note
			status: creator
		require
			valid_indexes: l <= u + 1
		do
			if l <= u then
				lower := l
				upper := u
			else
				lower := 1
				upper := 0
			end
			create area.make_filled (({G}).default, upper - lower + 1)
		ensure
			sequence_domain_definition: sequence.count = u - l + 1
			sequence_definition: across 1 |..| sequence.count as i all sequence [i] = ({G}).default end
			lower_definition: lower_ = if l <= u then l else 1 end
			no_observers: observers.is_empty
		end

	make_filled (l, u: INTEGER; v: G)
			-- Create array with indexes in [`l', `u']; set all values to `v'.
		note
			status: creator
		require
			valid_indexes: l <= u + 1
		do
			if l <= u then
				lower := l
				upper := u
			else
				lower := 1
				upper := 0
			end
			create area.make_filled (v, u - l + 1)
		ensure
			sequence_domain_definition: sequence.count = u - l + 1
			sequence_definition: across 1 |..| sequence.count as i all sequence [i] = v end
			lower_definition: lower_ = if l <= u then l else 1 end
			no_observers: observers.is_empty
		end

feature -- Initialization

	copy_ (other: like Current)
			-- Initialize by copying all the items of `other'.
			-- Reallocate memory unless count stays the same.
		require
			observers_open: across observers as o all o.is_open end
		do
			if other /= Current then
				check other.inv end
				if area = Void or other.count /= upper - lower + 1 then
					create area.make_filled (({G}).default, other.count)
				end
				check area.inv end
				area.copy_data (other.area, 0, 0, other.count)
				lower := other.lower
				upper := other.upper
				check other.is_wrapped end
			end
		ensure
			observers_open: across observers as o all o.is_open end
			sequence_effect: sequence ~ old other.sequence
			lower_effect: lower_ = old other.lower_
			modify_model (["sequence", "lower_"], Current)
		end

feature -- Access

	item alias "[]" (i: INTEGER): G assign put
			-- Value associated with `i'.
		do
			check inv end
			Result := area [i - lower]
		end

feature -- Measurement

	lower: INTEGER
			-- Lower bound of index interval.

	upper: INTEGER
			-- Upper bound of index interval.

	count: INTEGER
			-- Number of elements.
		do
			check inv end
			Result := upper - lower + 1
		end

feature -- Iteration

	at (i: INTEGER): V_ARRAY_ITERATOR [G]
			-- New iterator pointing at position `i'.
		note
			status: impure
			explicit: wrapping
		do
			check inv end
			create Result.make (Current, i - lower + 1)
		end

feature -- Comparison

	is_equal_ (other: like Current): BOOLEAN
			-- Is array made of the same items as `other'?
			-- (Use reference comparison.)
		do
			check inv; other.inv end
			if other = Current then
				Result := True
			elseif lower = other.lower and upper = other.upper then
				Result := area.same_items (other.area, 0, 0, count)
			end
		end

feature -- Replacement

	put (v: G; i: INTEGER)
			-- Put `v' at position `i'.
		do
			area.put (v, i - lower)
		end

	fill (v: G; l, u: INTEGER)
			-- Put `v' at positions [`l', `u'].
		do
			check area.inv end
			area.fill_with (v, l - lower, u - lower)
		end

	clear (l, u: INTEGER)
			-- Put default value at positions [`l', `u'].
		do
			area.fill_with_default (l - lower, u - lower)
		end

feature -- Resizing

	

	wipe_out
			-- Remove all elements.
		require
			observers_open: across observers as o all o.is_open end
		do
			create area.make_empty (0)
			lower := 1
			upper := 0
		ensure
			sequence_effect: sequence.is_empty
			lower_effect: lower_ = 1
			modify_model (["sequence", "lower_"], Current)
		end

feature {V_CONTAINER, V_ITERATOR} -- Implementation

	area: V_SPECIAL_2 [G]
			-- Memory area where elements are stored.
feature -- Specification

	is_model_equal (other: like Current): BOOLEAN
			-- Is the abstract state of `Current' equal to that of `other'?
		note
			status: ghost, functional
		do
			Result := sequence ~ other.sequence and lower_ = other.lower_
		end

invariant
	area_exists: area /= Void
	lower_definition: lower_ = lower
	upper_definition: upper = lower_ + sequence.count - 1
	owns_definition: owns ~ create {MML_SET [ANY]}.singleton (area)
	sequence_implementation: sequence ~ area.sequence

note
	explicit: observers
	date: "$Date: 2021-07-15 20:57:26 +0800 (Thu, 15 Jul 2021) $"
	revision: "$Revision: 105637 $"
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
