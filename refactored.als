// 17-724 Advanced Formal Method
// Final Project: Modeling Sesame Algorithm
// Ben Gafford and Simon Chu
// Dec 9, 2020

//-------------------
// define all signatures
//-------------------

sig Device {
	// User_Record that is associated with the User that is currently using the device
	current_user_record : one User_Record, 
	user_records : some User_Record, // list of all User_Record on the device
	id : one Device_ID,
	keys : one Key_Pair,
	elapsed_time : Int
}

some sig InitDevice in Device {}
{
	elapsed_time = 0
}

pred device_invariants [s : Server] {
	// devices unique to users
	// each user has a unique id 
	all u : s.users | { 
		let others = (s.users - u) | {
			u.devices not in others.devices 
			u.id not in others.id
		}
	}
}

run device_invariants for 3

sig Server {
	users : User,
	device_mail : Device -> one Mailbox,
	messages : Message
}

sig User_Record {
	id : one User_ID,
	device_records : Device_Record, 
	stale : Int, // mark the time the user record has been in the stale state, -1 for active
	known_devices_keys : Public_Key // user identity keys
}

sig Device_Record {
	id : one Device_ID,
	active_session : lone Session,
	inactive_sessions : Session,
	stale : Int // mark the time the device record has been in the stale state, -1 for active
}

sig User {
	id : one User_ID,
	devices : some Device
}

sig Message {
	device_ID : one Device_ID,	// Device_ID for the sender
	user_ID : one User_ID,		// User_ID for the sender
	content: one Content // content for the message
}

sig Mailbox {
	messages : Message
}

sig Session {
	id : one Session_ID
}

sig Key_Pair {
	private_key : one Private_Key,
	public_key : one Public_Key
}

sig Private_Key {}

sig Public_Key {}

sig Content {}

sig Session_ID {}

sig Device_ID {}

sig User_ID {}


//--------------------------------------------------
// update device state (section 3.2, sesame documentation)
//--------------------------------------------------

// delete User_Record from Device state
pred delete_user_record[d, d': Device, ur: User_Record] {
	// pre-condition:
	// User_Record "ur" exists in Device "d"
	ur in d.user_records

	// post-condition:
	// user record "ur" is deleted from Device "d"
	// increment elapsed_time
	d'.user_records = d.user_records - ur
	d'.elapsed_time = d'.elapsed_time + 1

	// frame condition:
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
}

run delete_user_record for 3

// delete Device_Record from Device state
pred delete_device_record[d, d': Device, dr: Device_Record] {
	// pre-condition:
	// Device_Record "dr" exists in the Device "d"
	dr in d.user_records.device_records

	// post-condition:
	// Device_Record "dr" is removed.
	// If "dr" is the last Device_Record in a User_Record "ur", remove the User_Record "ur".
	// increment the elapsed_time
	all ur: User_Record | (ur in d.user_records and ur.device_records = {dr}) =>delete_user_record[d, d', ur]
	d'.user_records.device_records = d.user_records.device_records - dr
	d'.elapsed_time = d.elapsed_time + 1

	// frame condition:
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
}

// TODO: understand the code
pred delete_session[d, d': Device, s: Session] {
	let ss = d.user_records.device_records.active_session + d.user_records.device_records.inactive_sessions | {

	// precond: s is some session in d
	s in ss

	// postcond: 
	// the Session is removed. if it is the last Session for a given DeviceRecord, remove that DeviceRecord as well
	d'.user_records.device_records.active_session = (d.user_records.device_records.active_session - s) or 
	d'.user_records.device_records.inactive_sessions = (d.user_records.device_records.inactive_sessions - s) or
		some dr : Device_Record | delete_device_record[d,d',dr] and ss = {s}
	
	// frame conditions
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time + 1 // Should we update time??
	}
}

// insert_session operation (promotion pattern)
pred insert_session_global[d, d': Device, s: Session] {
	some dr, dr': Device_Record |
		insert_session_promote[d, d', dr, dr', s] and
		insert_session_local[dr, dr', s]

	// frame condition for global state Device
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time + 1
}

pred insert_session_local[dr, dr': Device_Record, s: Session] {
	// describe changes to local state Device_Record
	dr'.active_session = s
	dr'.inactive_sessions = dr.active_session + dr.inactive_sessions
	dr'.stale = dr.stale
}

pred insert_session_promote[d, d': Device, dr, dr': Device_Record, s: Session] {
	// describe how global state Device and local state Device_Record relate to each other in the insert_session operation
	dr' in d'.user_records.device_records
	dr in d.user_records.device_records
	d'.user_records.device_records = d.user_records.device_records - dr + dr'
}


// activate_session operation (promotion pattern)
pred activate_session_global[d, d': Device, s: Session] {
	some dr, dr': Device_Record |
		activate_session_promote[d, d', dr, dr', s] and
		activate_session_local[dr, dr', s]

	// frame condition
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time
}

pred activate_session_local[dr, dr': Device_Record, s: Session] {
	// pre-condition
	s in dr.inactive_sessions

	// post-condition
	dr'.active_session = s
	dr'.inactive_sessions = dr.inactive_sessions - s + dr.active_session

	// frame condition
	dr'.stale = dr.stale

}

pred activate_session_promote[d, d': Device, dr, dr': Device_Record, s: Session] {
	dr in d.user_records.device_records
	dr' in d'.user_records.device_records
	d'.user_records.device_records = d.user_records.device_records - dr + dr'
}


// TODO: convert to promotion pattern
pred mark_user_record_stale[d, d': Device, ur, ur': User_Record] {
	// pre-condition:
	// User_Record "ur" and "ur'" exists in the old and new Device state "d" and "d'"
	ur in d.user_records
	ur' in d'.user_records

	// post-condition:
	// mark the user_record stale based on the Device elapsed_time
	ur'.stale = d.elapsed_time

	// update the device state with the new user_record
	d'.user_records = d.user_records - ur + ur'

	// frame condition:
	ur'.known_devices_keys = ur.known_devices_keys
	ur'.device_records = ur.device_records

	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time	
}

// TODO: convert to promotion pattern
pred mark_device_record_stale[d, d': Device, dr, dr': Device_Record] {
	// pre-condition:
	// Device_Records "dr" and "dr'" exists in the old and new Device state "d" and "d'"
	dr in d.user_records.device_records
	dr' in d'.user_records.device_records

	// post-condition:
	// mark the device_record stale based on the Device elapsed_time
	dr'.stale = d.elapsed_time

	// update the device state with the new device_record
	d'.user_records.device_records = d.user_records.device_records - dr + dr'

	// frame condition
	dr'.active_session = dr.active_session
	dr'.inactive_sessions = dr.inactive_sessions

	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time	
}

pred update_user_records[] {
	
}
// Update a device's records with some new user
pred update_records[d,d': Device, uid : User_ID, did : Device_ID, pub : Public_Key] {
	//precond: none
	//postcond:
	// new user_records are the old ones, minus any with the same uid, plus a new blank one with the new uid
	d'.user_records = 
		 { ur : d.user_records | { ur.id != uid or ur.known_devices_keys != pub}} + 
			{ new_ur : User_Record | { 
				{
				new_ur.known_devices_keys = {pub} 
				new_ur.stale = -1
				new_ur.id = uid
				new_ur.device_records = { dr : Device_Record | {
					no dr.active_session // not in encrypted
					no dr.inactive_sessions
					dr.stale = -1
					dr.id = did 
				} }
				}
				or some ur : d.user_records | {
				{	// or it already exists, but device doesn't exist
					ur.id = uid 
					did not in ur.device_records.id
					new_ur.device_records = ur.device_records + 
						{ dr : Device_Record | {
							no dr.active_session // not in encrypted
							no dr.inactive_sessions
							dr.stale = -1
							dr.id = did 
						} }

				}
				or {    // or it already exists, but device does exist
					ur.id = uid
					new_ur = ur
					did in ur.device_records.id
				}
				}
			} } 

	// frame conditions
	d'.current_user_record = d.current_user_record
	d'.id = d.id
	d'.keys = d.keys
	d'.elapsed_time = d.elapsed_time
}

run update_records for 3 but 2 Device

pred delete_stale_user_records[d,d' : Device, uid : User_ID, did : Device_ID] {
	// Delete the relevant UserRecord and/or DeviceRecord if they are stale
	// user records is the same as old user records, except remove this uid user if stale.
	d'.user_records = { ur : d.user_records | {
		ur.id != uid
	}} + { ur : d.user_records | { 
			ur.id = uid and ur.stale = -1 and ur in d.user_records }//and 
				//some dr : ur.device_records | dr.stale = -1 and dr.id = did}
			}
	
	some ur,ur' : User_Record | {
		promote_device_records[d,d',ur,ur']
		delete_stale_device_records_local[ur,ur',uid,did]
	}
}

pred delete_stale_device_records_local[ur,ur' : User_Record, uid : User_ID, did : Device_ID] {
	ur'.id = ur.id
	ur'.device_records = { dr : ur.device_records | { dr.id != did }} + 
		{ dr : ur.device_records | { 
			dr.id = did and dr.stale = -1 and dr in ur.device_records }
		}
}

pred promote_device_records[d,d' : Device, ur,ur' : User_Record] {
	ur in d.user_records
	d'.user_records = d.user_records - ur + ur'
}

pred prep_encryption[d,d' : Device, uid : User_ID, did : Device_ID, pub : Public_Key] {
	// 1. Delete the relevant UserRecord and/or DeviceRecord if they are stale
	//delete_stale_user_records[d,d',uid,did]

	// 2. Conditionally update records based on the tuple
	// NOTE: this version of conditionally updating doesn't force the activeSession to be empty
	update_records[d,d', uid, did, pub]
	
	// 3. If relevant DeviceRecord does not have active session, then the device 
	//    creates a new initiating session using the relevant public key for the 
	//    DeviceRecord. The new session is inserted into the DeviceRecord. 
	// TODO: uhh how do we make an initiating session using pub key???
	some {dr : d'.user_records.device_records | {
		one s : Session | dr.active_session = {s} // TODO "do we need to specify this as a new session, or is this implicit in existing constraints"
	}}
}


//-----------------------
// Sending and receiving messages [3.3]
//-----------------------

// sent message Content to to the user associated with the User_ID
// receipient must include device's own user ID
// TODO: set of receipients instead of only one
// TODO: send_message_to_server, fetch_message_from_server, receive_message
/*
// @uid: the User_ID of the recipient of the message
// send the message to the Server
pred send_message[s, s': Server, m: Message, uid: User_ID] {
	// TODO: User_Record must be non-stale

	// pre-condition:
	// User_Record exists for the recipient User_ID (User -> Device -> User_Record)
	some u: User, ur: User_Record {
		u.id = uid					// same user id
		ur in u.devices.user_records	// exists user_records
	
		// post-condition (add new device_mail mappings to the existing mappings in the device)
		some dm: Device -> Mailbox {
			// get all Device -> Mailbox mappings for the user
			{ d: u.devices {
				some mb: Mailbox {
					m in mb.messages 	// sender message must contain in the mailbox
					(d -> mb) in dm	// mapping must exist in the device_mail
				}
			}
			}
			s'.device_mail = s.device_mail + dm		
		//all d: u.devices | s'.device_mail = s'.device_mail + (d -> m) // don't know how to express.. add all to one mapping u.devices -> m to s'.device_mail mapping
		}
	}
	// post-condition:
	// get all devices of the message receipient
	// update the server.device_mail
}

pred receive_message[s, s': Server] {
}
*/
//-----------------------
// define system invariants
//-----------------------

pred invariant {
	// device current record should not overlap with previous record
	all d: Device | d.current_user_record in d.user_records

	// device record active session should not overlap with inactive record
	all dr: Device_Record | dr.active_session not in dr.inactive_sessions
}

pred security_invariants {
	// Encrypting message requires creating sessions for sending 
   // device to each receiving device owned by a user
	
	// When a device is removed, that device cannot receive new messages (but can read old msgs**)
	// When a device is added, that device can receive new messages (but cannot read old msgs**)
	// Sessions can be initiated simulatenously, they need to decide on a matching session
	// Either party's device session state can be reverted to some old state or cleared, and the "right thing" should happen
	// messages can arrive out of order, and clock synchronization is not reliable

	// With sesame, each device keeps track of a single "active" session for each other device it's communicating with
	// Also keeps track of "inactive" sessions, which can switch into being an active session if some activity occurs. 
	// Each device converges on a single session for each device
}

run default {
	invariant
	some Device
	no Server
}

run delete_user_record {
	invariant
	some d, d': Device, ur: User_Record | delete_user_record[d, d', ur]
}

run delete_device_record {
	invariant
	some d, d': Device, dr: Device_Record | delete_device_record[d, d', dr]
}

/*
run send_message {
	invariant
	some s, s': Server, m: Message, uid: User_ID | send_message[s, s', m, uid]
}
*/

//todo: add fact that all devices by a user share the identity keypair
