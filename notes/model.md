https://alloy.readthedocs.io/en/latest/language/predicates-and-functions.html

- each device keep track of an (active session -> each other device)
- use the active session when sending to that device
- maybe ignore active/inactive sessions for now

session is a channel/bridge between devices
Device-1 <-> Session <-> Device-2

User_Record -> Device_Record -> Sessions

matching sessions: 

Session {
    messages: Message // message sent via the session
    from: one Device // the device the message is sent from
    to: one Device // the device message is sent to
    isActive: True/False
}

- Alice -> Bob
- sending message for the first time (create session from device_1 to device_2)
- 

Question: what determines the active/inactive of the session? (elapsed time)
what is a matching session?

Properties to check
- when a device is removed, that device cannot receive new messages
- if remove_device(device_record, user_record) => !can_receive_new_messages(device_record, user_record)
    - can_receive_new_messages ensure device_record is in a user_record

- when a device is added, the device can receive new messages, but cannot read old messages (from other devices)
- if add_device(device_record, user_record) => can_receive_new_messages(device_record, user_record)
- No middleman (attacker) from the Server or ISP that has the encrypted message can decrypt the message other than Alice herself

Ben suggested Property:
- we not are trusting the server ( WE trust the server as little as possible)
    - make a new credential for itself
- when a device is added, the device can receive new messages, but cannot read old messages (from other devices)
    - getting sent a message

    
    - all user: User | encrypted_message in User, decrypted(user, encrypted message) => user = Alice


Ben:
active_session: managing the messages I'm sending to you


User_Record enables Device_Record to send outbound messages to user's other devices