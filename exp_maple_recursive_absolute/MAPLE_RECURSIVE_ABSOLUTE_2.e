class
	MAPLE_RECURSIVE_ABSOLUTE_2

feature
	abs (x: INTEGER): INTEGER
		do
			if x >= 0 then
				Result := x
			else
				Result := x
			end
		ensure
			arg_when_arg_non_negative: x >= 0 implies Result = x
			negative_when_arg_negative: x < 0 implies Result = -x
		end
end
