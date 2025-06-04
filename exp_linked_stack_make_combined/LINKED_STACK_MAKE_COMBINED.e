class
	LINKED_STACK_MAKE_COMBINED [G]

create
	buggy_make

feature
	buggy_make
		do
			before := True
		end

	before, after: BOOLEAN
	count: INTEGER
	active, first_element, last_element: detachable V_LINKABLE [G]

invariant
	empty_constraint: (count = 0) implies ((first_element = Void) and (active = Void))
	active_empty: (active = Void) = (count = 0)
	before_constraint: before implies (active = first_element)
	after_constraint: after implies (active = last_element)

		-- from BILINEAR
	not_both: not (after and before)

end
