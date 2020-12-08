// Mon 2020-12-07 17:01:52 EST

sig Server {
    user_records: set User_Record, // (0 or more) record of all users registered in the server
    device_mail: Device_Record -> one Mailbox // store unfetched messages for each device in the Mailbox
}

sig User_Record {
	device_records: set Device_Record, // (0 or more) records all devices that user owns
    id: one User_ID,
    known_devices: set Public_Key // set of public_keys for known devices (from other users) for message decryption purposes
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
    ur'.known_devices = ur.known_devices
}

pred delete_device_record[ur, ur': User_Record, dr: Device_Record] {
    // add Device_Record to the User_Record

    // pre-condition: Device_Record exists in the User_Record
    dr in ur.device_records

    // post-condition: Device_Record is deleted from the User_Record
    ur'.device_records = ur.device_records - dr

    // frame condition
    ur'.id = ur.id
    ur'.known_devices = ur.known_devices
}

// fun create_message_from_text[pt: Plain_Text]{
// 
// }

// helper functions
fun create_matching_intiaiting_session[s: Initiating_Session]: Initiating_Session {
    // create a matching session for the initiating session
    { s': Initiating_Session {
            s'.id = s.id
            s'.from = s.to // flip the from and to field for the matching session
            s'.to = s.from
            s'.public_key = s.public_key
        }
    }
}

fun create_matching_regular_session[s: Regular_Session]: Regular_Session {
    // create a matching sessino for the regular session
    { s': Regular_Session {
            s'.id = s.id
            s'.from = s.to // flip the from and to field for the matching session
            s'.to = s.from
            s'.messages = s.messages
        }
    }
}
                                  // sender/destination      // sending device
pred send_message[pt: Plain_Text, u_from, u_to, u_to': User_Record, dr_from, dr_from': Device_Record] {

    // encapsulate the message first

    // if no session exists, create_initiating_session
    // if session exists, send

}

// given the device records for the sender and the receiver, create initiating sessions

pred create_initiating_session[dr_from, dr_from', dr_to, dr_to': Device_Record] {
    // dr_from.sessions
    // intiating session will turn to regular session at the end

    // intiating session created will exchanges public keys of the devices
}

pred fetch_public_key_from_initiating_session[] {

}

pred delete_session[] {

}

pred create_regular_session[] {

}


pred encrypt_message[] {

}

// decrypt the ciphered text on device
pred decrypt_message[m, m': Message, dr: Device_Record] {
    // pre-condition:
    // device must has the private key needed 
}


// offline scenario, send message to the server
pred send_message_to_server {

}

// offline -> online scenario, fetch/receive message from the server
pred receive_message_from_server {

}

// system invariants that should be preserved by each operation
pred invariants {
}




//----------
// Functions
//----------

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

check Always_Decrypt for 3

assert Matching_Session_Property {
    // all s, s': Initiating_Session | s' = create_matching_initiating_session[s'] 
    all s, s': Initiating_Session {
        s' = create_matching_intiaiting_session[s] => {
            s.from = s'.to
            s.to = s'.from
            s.public_key = s.public_key
        } 
    }

    all s, s': Regular_Session {
        s' = create_matching_regular_session[s] => {
            s.from = s'.to
            s.to = s'.from
            s.messages = s'.messages
        }
    }
}

check Matching_Session_Property for 3
//-------------------
// Run/Test Instances
//-------------------

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

// demonstrate the create_matching_session function
run create_matching_initiating_session_run {
    some s, s': Initiating_Session | s' = create_matching_intiaiting_session[s]
} for 5 
but 2 Private_Key,
    2 Public_Key,
    0 Server,
    0 User_Record,
    4 Device_Record,
    2 Initiating_Session,
    0 Regular_Session,
    0 Message,
    2 Session_ID,
    2 Device_ID,
    2 User_ID,
    // 1 Init_Sever_State,
    0 Text,
    0 Plain_Text,
    0 Cipher_Text,
    0 Mailbox