class
    FIND_FIRST_IN_SORTED_1

feature
	buggy_find_first_in_sorted (arr: SIMPLE_ARRAY [INTEGER]; key: INTEGER): INTEGER
		require
			length_is_positive: 0 <= arr.count
			is_sorted: across 1 |..| arr.count  as j all across 1 |..| (j - 1)  as i all arr.sequence [i] <= arr.sequence [j] end end
			k1: 0 <= key and key <= 10 and arr.count <= 10 and across 1 |..| arr.count  as i all 0 <= arr.sequence [i] and arr.sequence [i] <= 10 end
		local
			low, high, mid: INTEGER
			found: BOOLEAN
		do
			from
				low := 1
				high := arr.count + 1
				found := False
				Result := -1
			invariant
				low_in_range: 1 <= low and low <= arr.sequence.count + 1
				high_in_range: 1 <= high and high <= arr.sequence.count + 1
				low_is_lower: low <= high
				low_did_not_miss: across 1 |..| (low - 1)  as i all arr.sequence [i] < key end
				high_did_not_miss: across (high + 1) |..| arr.sequence.count  as i all key <= arr.sequence [i] end

				if_not_found_strict_inequality: not found implies (across high |..| arr.sequence.count  as i all key < arr.sequence [i] end)
				result_in_range: Result = -1 or (low <= Result and Result <= high - 1)
				if_found_it_is_in_range: found implies (across low |..| (high - 1)  as i some arr.sequence [i] = key end)
				if_result_it_is_correct: (1 <= Result and Result <= arr.sequence.count) implies (arr.sequence [Result] = key and (across 1 |..| (Result - 1)  as i all arr [i] /= key end))

			until
				low > high
			loop
				mid := (low + high) // 2
				if arr [mid] = key then
					found := True
					if (mid = 1 or else (key /= arr [mid - 1])) then
						Result := mid
					else
						high := mid
					end
				elseif key < arr [mid] then
					high := mid
				else
					low := mid + 1
				end
			variant
				high - low + arr.count - Result
			end
		ensure
			result_not_too_big: Result <= arr.sequence.count
			lowest_result_found: (1 <= Result and Result <= arr.sequence.count) implies (arr.sequence [Result] = key and (across 1 |..| (Result - 1)  as i all arr [i] /= key end))
			neg_one_if_not_present: (Result = -1) implies (across 1 |..| arr.sequence.count  as i all arr.sequence [i] /= key end)
		end

end
