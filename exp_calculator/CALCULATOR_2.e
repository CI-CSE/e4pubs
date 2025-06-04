class
	CALCULATOR_2

feature
	calculate (a_num1, a_num2: INTEGER; a_operator: CHARACTER): INTEGER
		require
			feasible_operation:
       			(a_operator = '+') or
       			(a_operator = '*') or
       			(a_operator = '-') or
       			(a_operator = '/' and a_num2 /= 0) or
       			(a_operator = '%%' and a_num2 /= 0) or
       			(a_operator /= '+' and a_operator /= '*' and a_operator /= '-' and a_operator /= '/' and a_operator /= '%%')
		do
			inspect a_operator
				when '+' then
					Result := a_num1 + a_num2
				when '-' then
					Result := a_num1 + a_num2
				when '*' then
					Result := a_num1 * a_num2
				when '/' then
					Result := a_num1 // a_num2
				when '%%' then
					Result := a_num1 \\ a_num2
				else
					Result := -1
    		end
		ensure
			valid_sum:
       			(a_operator = '+') implies Result = a_num1 + a_num2
			valid_product:
       			(a_operator = '*') implies Result = a_num1 * a_num2
			valid_minus:
       			(a_operator = '-') implies Result = a_num1 - a_num2
			valid_division:
       			(a_operator = '/' and a_num2 /= 0) implies Result = a_num1 // a_num2
			valid_modulo:
       			(a_operator = '%%' and a_num2 /= 0) implies Result = a_num1 \\ a_num2
			valid_none_of_the_common_operations:
       			(a_operator /= '+' and a_operator /= '*' and a_operator /= '-' and a_operator /= '/' and a_operator /= '%%') implies Result = -1
		end

end
