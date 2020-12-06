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

sig Server {
	users : User,
	device_mail : Device -> Mailbox,
	messages : Message
}

sig User_Record {
	device_records : Device_Record, 
	stale : Int, // mark the time the user record has been in the stale state, -1 for active
	known_devices_public_key : Public_Key // user identity keys
}

sig Device_Record {
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
	message : Message
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

pred delete_session[d, d': Device, s: Session] {

}

// TODO: use promotion instead
pred insert_session[d, d': Device, dr, dr': Device_Record, s: Session] {

}

// TODO: use promotion instead
pred activate_session[d, d': Device, dr, dr': Device_Record, s: Session] {

}

pred mark_user_stale[d, d': Device, ur, ur': User_Record] {

}

pred mark_device_stale[d, d': Device, dr, dr': Device_Record] {

}

// sent message Content to to the user associated with the User_ID
// receipient must include device's own user ID
// TODO: set of receipients instead of only one
pred send_message[c: Content, user_id: User_ID] {
	// TODO: User_Record must be non-stale

	// pre-condition:
	// User_Record exists for the recipient User_ID (User -> Device -> User_Record)
	some u: User, ur: User_Record | u.id = user_id and ur in u.devices.user_records

	// post-condition:
	
}

pred receive_message[] {
}

//-----------------------
// define system invariants
//-----------------------

pred invariant {
	// device current record should not overlap with previous record
	all d: Device | d.current_user_record in d.user_records

	// device record active session should not overlap with inactive record
	all dr: Device_Record | dr.active_session not in dr.inactive_sessions
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