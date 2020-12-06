Variable changes
- privKey -> privateKey
- pubKey -> publicKey

- selfRecord -> current_user_record
- records -> user_records

- delete device -> delete device records (you are not actually deleting the device, but the device records)

problems
- plain text as a member of a message
- when you use the same name relations, NO ERRORS!

Invariants
- current records should be in the records (for Device)
- active_session shouldn't be equal to inactive_session

shortcomings of Alloy
- inability (inexpressiveness) to model concurrency




Point Out Problems
- how to intialize Elapsed Time to 0 at the beginning?


Don't Know
- how to pass in a list of recipients
- line 75 - not understanding the "or" statement (deleting the user-record)
should that be changed to and instead
- How to properly update the elapsed time
- How to link Sessoin with the messages

Limitation of Alloy
- imperative mentality, using declarative statement

suggestions:
- abstract away unnecessary details (stale/elapsed_time)