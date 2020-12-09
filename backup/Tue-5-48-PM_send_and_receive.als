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
// TODO: change Server to Device (state)
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

// fun create_message_from_text[pt: Plain_Text]{
// 
// }


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
    one sid: Session_ID {
        sid not in dr_from.sessions.id
        sid not in dr_to.sessions.id

        // post-condition
        // add the created initiating_session to the sender and recipient device_records
        dr_from'.sessions = dr_from.sessions + create_initiating_session[dr_from, dr_to, sid]
        dr_to'.sessions = dr_to.sessions + create_initiating_session[dr_to, dr_from, sid]
    }

  
    // frame condition
    dr_from'.keys = dr_from.keys
    dr_from'.id = dr_from.id
    dr_to'.keys = dr_to.keys
    dr_to'.id = dr_to.id
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
            // s'.messages = {}
        }
    }
    // delete the initiating_session first before creating regular session

}

// given the device the message is sending from
// create the the regular session for the device based on the initiating session
// then delete the 
pred create_regular_session_for_device_record_from_initiating_session[dr_from, dr_from', dr_to, dr_to': Device_Record] {
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
        dr_from'.sessions = dr_from.sessions - s + create_regular_session_from_initiating_session[s]
        dr_to'.sessions = dr_to.sessions - s' + create_regular_session_from_initiating_session[s']
    }
}


                                  // sender/destination      // sending device
                                  // via the regular channel
pred send_message_to_server[s, s': Server, pt: Plain_Text, u_from, u_to, u_to': User_Record, dr_from, dr_from': Device_Record] {

    // encapsulate the message first

    // if no session exists, create_initiating_session
    // if session exists, send
    
    // pre-condition
    // check if regular session exists 
    // send message to the server first, in "receive_message" fetch the encrypted message from the server

}

// pred fetch_from_server
// decrypt the messages
// add them to the corresponding session in the session in the receipient (Via Session_ID)
// property check: everytime after the fetch from server, the messages fetched (in the receipient session) will be consistent between the sender and receipient (nothing being altered)

// given the device records for the sender and the receiver, create initiating sessions

// send message combines all operation, stream line operations
// easier for checking message
// check the message sent from User_1 to User_2 will be delivered to all User_1's other devices and User_1's all devices 


pred delete_session[] {

}

pred encrypt_message[] {

}

// decrypt the ciphered text on device
pred decrypt_message[m, m': Message, dr: Device_Record] {
    // pre-condition:
    // device must has the private key needed 
}



// offline -> online scenario, fetch/receive message from the server
pred receive_message_from_server {

}

// system invariants that should be preserved by each operation
pred invariants {
}




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

    // keypair and public/private keys must be unique to each device
    all kp: Key_Pair |
        one dr: Device_Record | dr.keys = kp
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

// // demonstrate the create_matching_session function
// run create_matching_initiating_session_run {
//     some s, s': Initiating_Session | s' = create_matching_intiaiting_session[s]
// } for 5 
// but 2 Private_Key,
//     2 Public_Key,
//     0 Server,
//     0 User_Record,
//     4 Device_Record,
//     2 Initiating_Session,
//     0 Regular_Session,
//     0 Message,
//     2 Session_ID,
//     2 Device_ID,
//     2 User_ID,
//     // 1 Init_Sever_State,
//     0 Text,
//     0 Plain_Text,
//     0 Cipher_Text,
//     0 Mailbox


// **DEMO**
// simple run
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
