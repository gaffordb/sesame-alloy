// Mon 2020-12-07 17:01:52 EST

sig Server {
    users: set User_Record // (0 or more) record of all users registered in the server
}

sig User_Record {
	device_records : set Device_Record // (0 or more) records all devices that user owns
}

sig Device_Record {
    sessions: set Session, // (0 or more) open sessions to communicate between the device and other devices
    keys: one Key_Pair // contains public/private key pair for device to encrypt/decrypt messages
}

sig Session {}

// Initiating_Session is Regular_Session with the public_key
sig Initiating_Session extends Session {
    messages: Message, // message sent via the session
    from: one Device_Record, // the device the message is sent from
    to: one Device_Record, // the device message is sent to
    public_key: one Public_Key // the public key needed to encrypt messages
}

sig Regular_Session extends Session {
    messages: Message, // message sent via the session
    from: one Device_Record, // the device the message is sent from
    to: one Device_Record // the device message is sent to
}

sig Message {
	sender_device_ID : one Device_ID,	// Device_ID for the sender
	sender_user_ID : one User_ID,		// User_ID for the sender
	content: one Text              // Text content for the message
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
}

pred send_message_via_regular_session[] {

}


pred encrypt_message[] {

}

// decrypt the ciphered text on device
pred decrypt_message[m, m': Message, dr: Device_Record] {
    // pre-condition:
    // device must has the private key needed
    
}

// decrypt the Cipher_Text
// Cipher_Text -> decrypt_text -> Plain_Text$(id=0)
// for visualization
fun decrypt_text[ct: Cipher_Text]: one Plain_Text {
    // given a cipher_text
    // return the Plain_Text associated with the Cipher_Text
    { pt: Plain_Text | pt = ct.plain_text }
}

// encrypt the Cipher_Text
// Plain_Text -> encrypt_text -> Cipher_Text
// for visualization
fun encrypt_text[pt: Plain_Text, pk: Public_Key]: one Cipher_Text {
    // given a plain_text
    // return the Cipher_Text encrypted from Plain_Text using Public_Key
    { ct: Cipher_Text | ct = pk.(pt.encryption) }
}


pred send_message_direct {

}

// system invariants that should be preserved by each operation
pred invariants {
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

// Define the initial state of the Server
some sig Init_Sever_State {

}

// simple check: a Cipher_Text can always be decrypted
assert Always_Decrypt {
    all ct: Cipher_Text | #decrypt_text[ct] = 1
}

check Always_Decrypt for 3

// simplest run
// present cipher/plain text (1-to-1 relationship) along
// with public key to decrypt the ciphered text

// - can use decrypt_text/encrypt_text function to check the encrypted/decrypted
// texts
run encrypt {
    // invariants
    #Cipher_Text > 2
    #Private_Key > 2
    #Key_Pair > 2
} 
for 6
but 3 Private_Key,
    3 Public_Key,
    0 Server,
    0 User_Record,
    0 Session,
    0 Message,
    0 Session_ID,
    0 Device_ID,
    0 User_ID,
    // 0 Text,
    1 Init_Sever_State