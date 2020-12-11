// Mon 2020-12-07 17:01:52 EST

sig Server {
    user_records: set User_Record, // (0 or more) record of all users registered in the server
    device_mail: Device_Record -> one Mailbox // store unfetched messages for each device in the Mailbox
}

sig User_Record {
	device_records: set Device_Record, // (0 or more) records all devices that user owns
    id: one User_ID,
    known_devices_keys: set Public_Key // set of public_keys for known devices (from other users) for message decryption purposes
}

sig Device_Record {
    sessions: set Session, // (0 or more) open sessions to communicate between the device and other devices
    keys: one Key_Pair, // contains public/private key pair for device to encrypt/decrypt messages
    id: one Device_ID
}

sig Session {
    from: one Device_Record, // the device the message is sent from
    to: one Device_Record, // the device message is sent to
    id: one Session_ID
    // have field stores matching session
}

// Initiating_Session is Regular_Session with the public_key
sig Initiating_Session extends Session {
    // messages: set Message, // message sent via the session
    public_key: one Public_Key // the public key needed to encrypt messages
}

sig Regular_Session extends Session {
    messages: set Message // message sent via the session
}

sig Message {
	sender_device_ID : one Device_ID,	// Device_ID for the sender
	sender_user_ID : one User_ID,		// User_ID for the sender
	content: one Text              // Text content for the message
}

sig Mailbox {
	messages : set Message
}

// super type for Cipher_Text and Plain_Text
sig Text {}

sig Cipher_Text extends Text {
    private_key: one Private_Key, // private key needed to decrypt the ciphered message
    plain_text: one Plain_Text        // plain text that it can be decrypted to
}

sig Plain_Text extends Text {
    // note that Plain_Text doesn't have a public_key associated with it
    // because any arbitrary public_key can encrypt a Plain_Text
    // ensure that each Public Key can only encrypt to one Cipher_Text
    encryption: set Public_Key -> Cipher_Text // cipher text that the plain text can be encrypted to
}

sig Key_Pair {
    private_key: one Private_Key,
    public_key: one Public_Key
}


sig Private_Key {}

sig Public_Key {}

sig Device_ID {}

sig User_ID {}

sig Session_ID {}

//------------------
// System Operations
//------------------

// Primitive Operations: Add and Delete User and Device Records
pred add_user_record[s, s': Server, ur: User_Record] {
    // add User_Record to the Server

    // pre-condition: User_Record ur is not in the Server
    ur not in s.user_records
    
    // post-condition: User_Record ur is added to the new Server State s'
    s'.user_records = s.user_records + ur 

    // frame condition
    s'.device_mail = s.device_mail
}

pred delete_user_record[s, s': Server, ur: User_Record] {
    // delete User_Record from the Server

    // pre-condition: User_Record ur is in the Server
    ur in s.user_records

    // post-condition: User_Record ur is deleted from the new Server State s'
    s'.user_records = s.user_records - ur

    // frame condition
    s'.device_mail = s.device_mail
}

pred add_device_record[ur, ur': User_Record, dr: Device_Record] {
    // add Device_Record to the User_Record

    // pre-condition: Device_Record does not exists in the User_Record
    dr not in ur.device_records

    // post-condition: Device_Record is deleted from User_Record
    ur'.device_records = ur.device_records + dr

    // frame condition
    ur'.id = ur.id
    ur'.known_devices_keys = ur.known_devices_keys
}

pred delete_device_record[ur, ur': User_Record, dr: Device_Record] {
    // add Device_Record to the User_Record

    // pre-condition: Device_Record exists in the User_Record
    dr in ur.device_records

    // post-condition: Device_Record is deleted from the User_Record
    ur'.device_records = ur.device_records - dr

    // frame condition
    ur'.id = ur.id
    ur'.known_devices_keys = ur.known_devices_keys
}

// add the session to device record
pred add_session[dr, dr': Device_Record, s: Session] {
    // pre-condition: session does not exist in the device
    s not in dr.sessions

    // post-condition: session is added to the device_record
    dr'.sessions = dr.sessions + s

    // frame condition
    dr'.keys = dr.keys
    dr.id = dr.id
}

pred delete_session[dr, dr': Device_Record, s: Session] {
    // pre-condition: session exists in the device
    s in dr.sessions

    // post-condition: session is deleted from the device
    dr'.sessions = dr.sessions - s

    // frame condition
    dr'.keys = dr.keys
    dr.id = dr.id
}



// helper function for create_initiating_session
// function to create a initiating session with a distinct Session_ID
fun create_initiating_session[dr_from, dr_to: Device_Record, sid: Session_ID]: Initiating_Session {
    { s: Initiating_Session {
        s.from = dr_from
        s.to = dr_to
        s.public_key = dr_to.keys.public_key // public key from the device (to send to) for message encryption
        s.id = sid // specify unique session ID through the parameter passed
    }  }
}

// Create the initiating session to exchange the public key between the sender device and receipient device
// the session created in the device_record contains the public key for the opposite device for encryption purposes
pred create_initiating_session_for_device_record[dr_from, dr_from', dr_to, dr_to': Device_Record] {
    // exchange public key via the matching session
    
    // pre-condition:
    // make sure devices are distinct (from and to device are different)
    not dr_from = dr_to

    // ensure a unique Session_ID bewtween matching sessions
    some sid: Session_ID {
        // pre-condition:
        // session ID should be unique with respect to the sessions
        // in the from/to Device_Record 
        sid not in dr_from.sessions.id
        sid not in dr_to.sessions.id

        // post-condition
        // add the created initiating_session to the sender and recipient device_records
        some sf: create_initiating_session[dr_from, dr_to, sid] |
            dr_from'.sessions = dr_from.sessions + sf
        // dr_from'.sessions = dr_from.sessions + create_initiating_session[dr_from, dr_to, sid]

        // create the matching initiating session
        some st: create_initiating_session[dr_to, dr_from, sid] |
            dr_to'.sessions = dr_to.sessions + st
        
        // dr_to'.sessions = dr_to.sessions + create_initiating_session[dr_to, dr_from, sid]
    }
  
    // post-condition
    not dr_from' = dr_from
    not dr_to' = dr_from

    not dr_to' = dr_to
    not dr_from' = dr_to

    not dr_from' = dr_to'

    // frame condition
    dr_from'.keys = dr_from.keys
    dr_from'.id = dr_from.id
    dr_to'.keys = dr_to.keys
    dr_to'.id = dr_to.id
}

// create initiating session from the user that the message is sent from to all other devices of the user and all recipient devices
pred create_initiating_session_for_sending[ur_from, ur_from', ur_to, ur_to': User_Record, dr_from, dr_from': Device_Record] {
    // pre-condition
    dr_from in ur_from.device_records

    // post-condition
    all dr_to: ur_to.device_records + ur_from.device_records - dr_from,
        dr_to': ur_to'.device_records + ur_from'.device_records - dr_from' {
        create_initiating_session_for_device_record[dr_from, dr_from', dr_to, dr_to']
    }

    dr_from' in ur_from'.device_records

    // frame condition
    ur_from'.id = ur_to.id
    ur_from'.known_devices_keys = ur_to.known_devices_keys

    dr_from'.keys = dr_from.keys
    dr_from'.id = dr_from.id
}

// given the device record and the initiating session from the device, extract the public key from the initiating
pred fetch_public_key_from_initiating_session[ur, ur': User_Record, s: Initiating_Session] {
    // pre-condition
    // ensure that the Initiating_Session s belongs to the Device_Record that belongs to the User_Record
    s in ur.device_records.sessions

    // post-condition: add the public_key from the session to the user_record for decryption
    ur'.known_devices_keys = ur.known_devices_keys + s.public_key
    
    // frame condition
    ur'.device_records = ur.device_records
    ur'.id = ur.id
}

// helper function
// create the regular session from the initiating session
// given the initiaiting session, convert to regular session with empty set of messages
fun create_regular_session_from_initiating_session[s: Initiating_Session]: Regular_Session {
    { s': Regular_Session {
            s'.from = s.from
            s'.to = s.to
            s'.id = s.id
            #s'.messages = 0 // create an empty set of messages
        }
    }
    // delete the initiating_session first before creating regular session

}

// given the device the message is sending from
// create the the regular session for the device based on the initiating session
// then delete the 
// convert the initiating session to the regular session
pred create_regular_session_for_device_record_from_initiating_session[dr_from, dr_from', dr_to, dr_to': Device_Record] {
    
    // pre-condition: make sure devices are distinct (from and to device are different)
    not dr_from = dr_to
    
    // pre-condition, both devices have initiation sessions to each other
    some s, s': Initiating_Session {
        // ensure the initiating session exists in the Device Records of the sender and recepient
        s in dr_from.sessions
        s' in dr_to.sessions
        
        // ensure s and s' are matching sessions (matching session IDs)
        s.id = s'.id

        // create the regular session based on the initiating session
        // meaning, converting the initiating sessions to regular sessions
        // add the regular session to the session list for the device record
        // then delete the initiating session

        // post-condition
        // add the created initiating_session to the sender and recipient device_records
        // ensure there are regular session created from the initiating sessions
        some sr: create_regular_session_from_initiating_session[s] |
            dr_from'.sessions = dr_from.sessions - s + sr

        some sr': create_regular_session_from_initiating_session[s'] |        
            dr_to'.sessions = dr_to.sessions - s' + sr'


        // frame condition
        dr_from'.keys = dr_from.keys
        dr_from'.id = dr_from.id

        dr_to'.keys = dr_to.keys
        dr_to'.id = dr_to.id
    }

    // post-condition, the resulting states should not be equivalent
    not dr_from' = dr_from
    not dr_to' = dr_from

    not dr_to' = dr_to
    not dr_from' = dr_to

    not dr_from' = dr_to'
}


// create initiating session from the user that the message is sent from to all other devices of the user and all recipient devices
pred create_regular_session_from_initiating_session_for_sending[ur_from, ur_from', ur_to, ur_to': User_Record, dr_from, dr_from': Device_Record] {
    // pre-condition
    dr_from in ur_from.device_records

    // post-condition
    all dr_to: ur_to.device_records + ur_from.device_records - dr_from,
        dr_to': ur_to'.device_records + ur_from'.device_records - dr_from' {
        create_regular_session_for_device_record_from_initiating_session[dr_from, dr_from', dr_to, dr_to']
    }

    dr_from' in ur_from'.device_records

    // frame condition
    ur_from'.id = ur_to.id
    ur_from'.known_devices_keys = ur_to.known_devices_keys

    dr_from'.keys = dr_from.keys
    dr_from'.id = dr_from.id
}

// helper function
// create/encapsulate a message based on sender device ID (sdid) and sender user ID (suid)
fun create_message_from_text[pt: Plain_Text, sdid: Device_ID, suid: User_ID]: Message {
    { m: Message {
            m.sender_device_ID = sdid
            m.sender_user_ID = suid
            m.content = pt
        }
    }
}

// helper function
// given the sender device record and user record, create the message
fun create_message_from_text_sender_user[pt: Plain_Text, sd: Device_Record, su: User_Record]: Message {
    {  m: Message {
            m = create_message_from_text[pt, sd.id, su.id]
        }
    }
}

// helper function
// encrypt message for a specific Device_Record to receive it
pred encrypt_message[m, m': Message, dr: Device_Record, ur: User_Record] {
    // pre-condition: User Record must have the public_key for encrypting for the Device_Record
    dr.keys.public_key in ur.known_devices_keys

    // post-condition: text is encrypted and stored back to the message
    m'.content = encrypt_text[m.content, dr.keys.public_key]
    
    // frame conditions
    m'.sender_device_ID = m.sender_device_ID
    m'.sender_user_ID = m.sender_user_ID
}

// helper function
// decrypt the ciphered text on device
pred decrypt_message[m, m': Message, dr: Device_Record] {
    // pre-condition:
    // usr must has the public key needed to decrypt the ciphered text in the message
    m.content.private_key = dr.keys.private_key

    // post condition: text is decrypted and stored in the message
    m'.content = decrypt_text[m.content]

    // frame conditions
    m'.sender_device_ID = m.sender_device_ID
    m'.sender_user_ID = m.sender_user_ID
}


// sender/destination      // sending device
// via the regular channel

// append the message (decrypted) in the session (sender device for sending)
// encrypt the message, append it to Server.device_mail Mailbox
// alter the server state
// alter the user_record state -> in particular device state -> append messages to the session established (from the sender to the recipient)
pred send_message_to_server[pt: Plain_Text, s, s': Server, ur_from, ur_from', ur_to: User_Record, dr_from, dr_from': Device_Record] {

    // if server has corresponding mailbox for the device, append
    // if not, add the mailbox for the device, and append the relation

    // if no session exists, create_initiating_session
    // if session exists, send
    
    // pre-condition
    // dr_from must be in ur_from (sender Device_Record must belong to sender User_Record)
    dr_from in ur_from.device_records
    ur_from in s.user_records
    ur_to in s.user_records

    // plain_text can be encrypted to an arbitrary Cipher_Text using the public key of the current device (that message is sent from)
    some ct: Cipher_Text | dr_from.keys.public_key -> ct in pt.encryption

    // there exists *active* regular sessions to establish the communication

    // TODO: given sender_user_record (ur_from), sender device (dr_from), receipient user_record (ur_to),
    // create initiating_session/convert_to_regular_session from sending_device (dr_from) to all sender's other devices
    // and all devicess for the recipient (ur_to.device_records)

    // naming conflict s: Server, s: Session
    // send message from the dr_from to ur_from's all other devices and recipients' all devices
    all dr: ur_from.device_records - dr_from + ur_to.device_records |
        some sid: Session_ID {//some : Regular_Session {
            // make sure there are established sessions first / there are matching regular sessions
            // all devices but the device that the message is sent from, must establish session connection 
            // all devices of the receipts must establish regular session connection with the sender
            sid in dr.sessions.id // s in all other devices of sender and receipient device
            // sid in dr'.sessions.id // s in all recipient devices
            sid in dr_from.sessions.id // matches the session in the sending device

            // post-condition
            // send message to the server first, in "receive_message" fetch the encrypted message from the server
            // append the message to the session in the sender (porting to self and other devices)
            some pm: Message, cm: Message {

                pm = create_message_from_text[pt, dr_from.id, ur_from.id]

                // encrypt the message to cm (ciphered message)
                encrypt_message[pm, cm, dr, ur_to]

                // append dr -> Mailbox(m), dr' -> Mailbox(m)
                // append message to the session of dr_from (dr_from'.sessions) and the server mailbox
                
                all sender_session: dr_from.sessions {
                    sender_session.id = sid

                    some sender_session': Regular_Session {

                        sender_session'.messages = sender_session.messages + pm // append the message to the sender sessions
                        sender_session'.id = sender_session.id
                        sender_session'.from = sender_session.from
                        sender_session'.to = sender_session.to

                        // post-condition
                        // replace the previous sender_session with the sender_session (with message appended) 
                        dr_from'.sessions = dr_from.sessions - sender_session + sender_session'
                    }
                }
            }
        }

    // update the mailbox***

    // post condition, update User_Record and Server state
    ur_from'.device_records = ur_from.device_records - dr_from + dr_from'
    s' = s.user_records - ur_from + ur_from'


    // encapsulate the message first

}

pred receive_message_from_server[s, s': Server, dr_to, dr_to': Device_Record] {
    // append the corresponding sessions
    // pre-condition:
    // the recipient Device_Records belongs to a registered User_Record in the Server
    dr_to in s.user_records.device_records

    // extract all messages that belongs to the Device_Record dr_to
    all cm: dr_to.(s.device_mail).messages { // all ciphered messages intended to be sent to dr_to
        some pm: Message {
            decrypt_message[cm, pm, dr_to]

            // decrypted message is pm
            some ur_from: User_Record, dr_from: Device_Record {
                ur_from.id = pm.sender_user_ID
                dr_from.id = pm.sender_device_ID
                dr_from = ur_from.device_records

                // find out matching sessions
                some receiver_session: Regular_Session {
                    receiver_session in dr_to.sessions

                    receiver_session.id in dr_from.sessions.id
                    receiver_session.id in dr_to.sessions.id

                    some receiver_session': Regular_Session{
                        receiver_session'.messages = receiver_session.messages + pm // append the message to the sender sessions
                        receiver_session'.id = receiver_session.id
                        receiver_session'.from = receiver_session.from
                        receiver_session'.to = receiver_session.to

                        // post-condition
                        // replace the previous sender_session with the sender_session (with message appended) 
                        dr_to'.sessions = dr_from.sessions - receiver_session + receiver_session'
                    }
                }
            }

        }
    }

    s'.user_records.device_records = s.user_records.device_records - dr_to + dr_to'
}

// add them to the corresponding session in the session in the receipient (Via Session_ID)
// property check: everytime after the fetch from server, the messages fetched (in the receipient session) will be consistent between the sender and receipient (nothing being altered)



// MAYBE: send message combines all operation, stream line operations
// easier for checking message
// check the message sent from User_1 to User_2 will be delivered to all User_1's other devices and User_1's all devices 

//-----------------------------
// Functions for Visualizations
//-----------------------------

// decrypt the Cipher_Text
// Cipher_Text -> decrypt_text -> Plain_Text$(id=0)
// for visualization purpose
fun decrypt_text[ct: Cipher_Text]: one Plain_Text {
    // given a cipher_text
    // return the Plain_Text associated with the Cipher_Text
    { pt: Plain_Text | pt = ct.plain_text }
}


// encrypt the Cipher_Text
// Plain_Text -> encrypt_text -> Cipher_Text
// for visualization purpose
fun encrypt_text[pt: Plain_Text, pk: Public_Key]: one Cipher_Text {
    // given a plain_text
    // return the Cipher_Text encrypted from Plain_Text using Public_Key
    { ct: Cipher_Text | ct = pk.(pt.encryption) }
}


//-------------
// Global Facts
//-------------
fact session_fact {
    all s: Session | not s.from = s.to
}

fact encryption_fact {
    // cipher_text and plain_text must be of symmetric relationship
    // meaning that if Cipher_Text$0.plain_text = Plain_Text$0;
    // then Plain_Text$0.cipher_text = Cipher_Text$0 (1-to-1 relationship)

    all ct: Cipher_Text, pt: Plain_Text {
        some pk: Public_Key {
            (ct.plain_text = pt) <=> (pk.(pt.encryption) = ct)
        }
    }

    // private keys must be unique to each keypair
    all priv_key: Private_Key {
        one kp: Key_Pair | no kp': Key_Pair | kp' != kp and kp'.private_key = priv_key
    }

    // continue: public keys must be unique to each keypair
    all pub_key: Public_Key {
        one kp: Key_Pair | no kp': Key_Pair | kp' != kp and kp'.public_key = pub_key
    }
}

// // Define the initial state of the Server
// some sig Init_Sever_State in Server{} {
//     // initial state of the Server
//     #user_records = 0 // no user_records
//     #device_mail = 0 // no device_mail mapping
// }

//------------------------
// Check System Properties
//------------------------

// simple check: a Cipher_Text can always be decrypted
assert Always_Decrypt {
    all ct: Cipher_Text | #decrypt_text[ct] = 1
}

check Always_Decrypt for 10

// ensure that when converting the initiating session to regular session
// the new regular session still matches (have matching Session_IDs)
// and the original Initiating_Session is deleted
assert creating_initiating_regular_session_preserve_session_matching {
    all dr_from, dr_from', dr_to, dr_to': Device_Record {
        { 
            // create the initiating sessions
            create_initiating_session_for_device_record[dr_from, dr_from', dr_to, dr_to']

            // create the regular session/delete the initiating session
            create_regular_session_for_device_record_from_initiating_session[dr_from, dr_from', dr_to, dr_to']
        }
        
            =>
        
        {
            some s, s': Regular_Session {
                s in dr_from'.sessions
                s' in dr_to'.sessions
                s.id = s'.id
            }
            // ensure the Initiating Session is deleted
            no s, s': Initiating_Session {
                s in dr_from'.sessions
                s' in dr_to'.sessions
                s.id = s'.id
            }
        }
    }
}

check creating_initiating_regular_session_preserve_session_matching for 10

assert initiating_session_created_are_matching_sessions {
    all dr_from, dr_from', dr_to, dr_to': Device_Record {
        create_initiating_session_for_device_record[dr_from, dr_from', dr_to, dr_to']
        => {
            some sf, st: Initiating_Session {
                sf = dr_from'.sessions - dr_from.sessions
                st = dr_to'.sessions - dr_to.sessions

                sf.id = st.id
                sf.from = st.to
                sf.to = st.from
            }
        }
    }
}

check initiating_session_created_are_matching_sessions for 10

// assert Matching_Session_Property {
//     // all s, s': Initiating_Session | s' = create_matching_initiating_session[s'] 
//     // all s, s': Initiating_Session {
//     //     s' = create_matching_intiaiting_session[s] => {
//     //         s.from = s'.to
//     //         s.to = s'.from
//     //         s.public_key = s.public_key
//     //     } 
//     // }

//     all s, s': Regular_Session {
//         s' = create_matching_regular_session[s] => {
//             s.from = s'.to
//             s.to = s'.from
//             s.messages = s'.messages
//         }
//     }
// }

// check Matching_Session_Property for 3

//-------------------
// Run/Test Instances
//-------------------


// demonstrate the add_user_record operation
run add_user_record_run {
    some s: Server, s': Server, ur: User_Record | add_user_record[s, s', ur]
} for 5 
but 0 Private_Key,
    0 Public_Key,
    2 Server,
    2 User_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    0 Device_ID,
    2 User_ID,
    // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox

// demonstrate the delete_user_record operation
run delete_user_record_run {
    some s: Server, s': Server, ur: User_Record | delete_user_record[s, s', ur]
} for 5 
but 0 Private_Key,
    0 Public_Key,
    2 Server,
    2 User_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    0 Device_ID,
    2 User_ID,
    // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox


// demonstrate the add_device_record operation
run add_device_record_run {
    some ur, ur': User_Record, dr: Device_Record | add_device_record[ur, ur', dr]
} for 5 
but 2 Private_Key,
    2 Public_Key,
    2 Server,
    2 User_Record,
    2 Device_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    2 Device_ID,
    2 User_ID,
    // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox

// demonstrate the add_device_record operation
run delete_device_record_run {
    some ur, ur': User_Record, dr: Device_Record | delete_device_record[ur, ur', dr]
} for 5 
but 2 Private_Key,
    2 Public_Key,
    2 Server,
    2 User_Record,
    2 Device_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    2 Device_ID,
    2 User_ID,
    // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox


// demonstrate creating the initiating session for device record
run create_initiating_session_for_device_record_run {
    some df, df', dt, dt': Device_Record |
        create_initiating_session_for_device_record[df, df', dt, dt']
} for 5 
but 2 Private_Key,
    2 Public_Key,
    0 Server,
    0 User_Record,
    // 4 Device_Record
    // 2 Session,
    0 Message,
    // 2 Session_ID,
    // 2 Device_ID,
    0 User_ID,
    // // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox

// demonstrate creating the initiating session for device record
run create_regular_session_for_initiating_session_run {
    some df, df', dt, dt': Device_Record |
        create_regular_session_for_device_record_from_initiating_session[df, df', dt, dt']
} for 5 
but 2 Private_Key,
    2 Public_Key,
    0 Server,
    0 User_Record,
    // 4 Device_Record
    // 2 Session,
    0 Message,
    // 2 Session_ID,
    // 2 Device_ID,
    0 User_ID,
    // // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox



// demonstrate encryption
// present cipher/plain text (1-to-1 relationship) along
// with public key to decrypt the ciphered text

// - can use decrypt_text/encrypt_text function to check the encrypted/decrypted
// texts
run encrypt_run {
    // invariants
    #Cipher_Text > 2
    #Private_Key > 2
    #Key_Pair > 2
} 
for 6
but 3 Private_Key,
    3 Public_Key,
    3 Device_ID,
    0 Server,
    0 User_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    0 User_ID,
    // 1 Init_Sever_State,
    0 Mailbox
