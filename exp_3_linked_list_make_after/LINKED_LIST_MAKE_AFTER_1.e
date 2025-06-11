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

invariant
	not_both: not (after and before)

end
