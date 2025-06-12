class
	LINKED_LIST_MAKE_AFTER_1

create
	buggy_make

feature
	buggy_make
		do
			before := True
		ensure
			is_before: before
		end

	before, after: BOOLEAN
	-- Before and after are used to see whether the current position in the linked list
	-- is before the first element or after the last element.

invariant
	not_both: not (after and before)

end
