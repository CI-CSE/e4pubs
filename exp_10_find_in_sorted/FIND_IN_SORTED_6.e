class
	FIND_IN_SORTED_6
feature
	buggy_binary_search (a_arr: SIMPLE_ARRAY [INTEGER]; a_x, a_start, a_end: INTEGER): INTEGER
		require
			decreases (a_end - a_start)
			a_start_a_end_bounds: 1 <= a_start and 1 <= a_end and a_start <= a_end and a_end <= (a_arr.sequence.count + 1)
			a_arr_sorted: across 1 |..| a_arr.sequence.count  as j all across 1 |..| (j - 1)  as i all a_arr.sequence [i] <= a_arr.sequence [j] end end
		local
			mid: INTEGER
		do
			if a_start = a_end then
				Result := 0
			else
				mid := a_start + (a_end - a_start) // 2
				if a_x <= a_arr [mid] then
					Result := buggy_binary_search (a_arr, a_x, a_start, mid)
				elseif a_x > a_arr [mid] then
					Result := buggy_binary_search (a_arr, a_x, mid + 1, a_end)
				else
					Result := mid
				end
			end
		ensure
			result_found: (1 <= Result and Result <= a_arr.sequence.count) implies a_arr.sequence [Result] = a_x
			result_sorted: (a_start < a_end and 1 <= Result and Result < a_end) implies (a_arr.sequence [a_start] <= a_arr.sequence [Result] and a_arr.sequence [Result] <= a_arr.sequence [a_end - 1])
			result_in_a_array: Result < a_end
			result_empty_a_array: (a_start = a_end) implies Result = 0
			result_not_found: (Result = 0) implies (across a_start |..| (a_end - 1)  as i all a_arr.sequence [i] /= a_x end)
		end

	find_in_sorted (a_arr: SIMPLE_ARRAY [INTEGER]; a_x: INTEGER): INTEGER
		require
			a_arr_not_empty: a_arr.sequence.count > 0
			a_arr_sorted: across 1 |..| a_arr.sequence.count  as j all across 1 |..| (j - 1)  as i all a_arr.sequence [i] <= a_arr.sequence [j] end end
		do
			Result := buggy_binary_search (a_arr, a_x, 1, (a_arr.count + 1))
		ensure
			result_found: (1 <= Result and Result < (a_arr.sequence.count + 1)) implies a_arr.sequence [Result] = a_x
			result_not_found: (Result = 0) implies (across 1 |..| a_arr.sequence.count  as i all a_arr.sequence [i] /= a_x end)
		end
end

