class
	QS_QUEUE_49
create
	make
feature {NONE}
	make
		note
			status: creator
			explicit: contracts, wrapping
		do
			front := 1
			rear := 1
			exception_is_raised := False
		ensure
			exception_not_raise: exception_is_raised = False
			front_is_front: front = 1
			rear_is_front: rear = 1
		end
feature
	max: INTEGER = 100
	front: INTEGER
	rear: INTEGER
	exception_is_raised: BOOLEAN
	queue: SIMPLE_ARRAY [INTEGER]
		attribute
			Result := create {SIMPLE_ARRAY [INTEGER]}.make (max)
		end

	enter (data: INTEGER)
		note
			explicit: wrapping
		require
			is_wrapped: is_wrapped
		do
			if not is_full then
				unwrap
				queue [rear] := data
				rear := rear + 1
				wrap
			else
				unwrap
				exception_is_raised := True
				wrap
			end
		ensure
			if_full: (old is_full) implies exception_is_raised
			not_full_rear: not (old is_full) implies (old rear) = rear - 1
			not_full_set: not (old is_full) implies queue.sequence [rear - 1] = data
		end

	delete: INTEGER
		note
			status: impure
			explicit: wrapping, contracts
		require
			is_wrapped: is_wrapped
		local
			poll, i: INTEGER
		do
			if not is_empty then
				from
					poll := queue [front]
					i := 1
				invariant
					rear_stays: rear = rear.old_
					is_wrapped: is_wrapped

					shifted_until_now: across i |..| (rear - 1) as j all queue.sequence [j] = queue.sequence.old_ [j] end
					shifted_until_now: across 1 |..| (i - 1) as j all queue.sequence [j] = queue.sequence.old_ [j + 1] end
					i_in_range: 1 <= i and i < rear

				until
					i + 1 >= rear
				loop
					unwrap
					queue [i] := queue [i + 1]
					wrap
					i := i + 1
				variant
					max - i
				end
				unwrap
				rear := rear - 1
				wrap
				Result := poll
			else
				unwrap
				exception_is_raised := True
				wrap
			end
		ensure
			is_wrapped: is_wrapped
			modify: modify_field (["exception_is_raised", "rear", "queue", "closed"], Current)
			if_empty: (old (rear = front)) implies exception_is_raised
			not_empty_rear: not (old (rear = front)) implies rear = (old rear - 1)
			not_empty_result: not (old (rear = front)) implies Result = (old queue.sequence [front])
			not_empty_queue: not (old (rear = front)) implies across 1 |..| (rear - 1) as j all queue.sequence [j] = (old queue.sequence) [j + 1] end
		end

	peek: INTEGER
		note
			explicit: wrapping
		require
			is_fully_writable
			is_wrapped: is_wrapped
		do
			if not is_empty then
				Result := queue [front]
			else
				unwrap
				exception_is_raised := True
				wrap
			end
		ensure
			if_empty: is_empty implies exception_is_raised
			if_not_empty: not is_empty implies Result = queue.sequence [front]
		end

	is_contain (key: INTEGER): BOOLEAN
		local
			index: INTEGER
		do
			from
				Result := False
				index := 1
			invariant
				index_in_range: 1 <= index and index <= rear
				not_found_until_now: across 1 |..| (index - 1) as i all queue.sequence [i] /= key end
				if_found: Result implies across 1 |..| (rear - 1) as i some queue.sequence [i] = key end
			until
				index >= rear or Result
			loop
				if key = queue [index] then
					Result := True
				else
					index := index + 1
				end
			variant
				max - index - if Result then 1 else 0 end
			end
		ensure
			if_found: Result implies across 1 |..| (rear - 1) as i some queue.sequence [i] = key end
			not_found: not Result implies across 1 |..| (rear - 1) as i all queue.sequence [i] /= key end
		end

	search (key: INTEGER): INTEGER
		local
			index: INTEGER
		do
			from
				index := 1
				Result := -1
			invariant
				result_positive: Result /= 0
				index_in_range: 1 <= index and index <= rear
				not_found: across 1 |..| (index - 1) as i all queue.sequence [i] /= key end
				if_in_range_then_correct: 1 <= Result and Result < rear implies queue.sequence [Result] = key
			until
				index >= rear or Result /= -1
			loop
				if key = queue [index] then
					Result := index
				else
					index := index - 1
				end
			variant
				max - index - if Result = -1 then 0 else 1 end
			end
		ensure
			res_not_zero: Result /= 0
			if_in_range_then_correct: 1 <= Result and Result < rear implies queue.sequence [Result] = key
			if_not_found_then_not_exists: Result = -1 implies across 1 |..| (rear - 1) as i all queue.sequence [i] /= key end
		end

	is_empty: BOOLEAN
		do
			Result := get_rear = get_front
		ensure
			result_is_correct: Result = (rear = front)
		end

	is_full: BOOLEAN
		do
			if max + 1 = get_rear then
				Result := True
			else
				Result := False
			end
		ensure
			resuld_is_correct: Result = (max + 1 = rear)
		end

	size: INTEGER
		do
			Result := rear - 1
		ensure
			result_is_correct: Result = rear - 1
		end

	get_front: INTEGER
		do
			Result := front
		ensure
			result_is_correct: Result = front
		end

	get_rear: INTEGER
		do
			Result := rear
		ensure
			result_is_correct: Result = rear
		end

	get_elem (i: INTEGER): INTEGER
		require
			i_in_range: 1 <= i and i < rear
		do
			Result := queue [i]
		ensure
			result_is_correct: Result = queue.sequence [i]
		end

invariant
    queue_not_void: queue /= Void
	owns_queue: owns = (create {MML_SET [ANY]}.singleton (queue))
	rear_in_range: 1 <= rear and rear <= max + 1
	front_is_front: front = 1
	queue_length: queue.sequence.count = max


end
