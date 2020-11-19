open util/boolean

let MAXLATENCY = 10

sig Server {
	users : User,
	deviceMail : Device -> Mailbox,
	messages : Message
}

sig User {
	uid : one UserID,
	uDevices : some Device
}
	
sig Device {
	selfRecord : one UserRecord,
	did : one DeviceID,
	records : UserRecord,
	keys : one KeyPair,
	elapsedTime : Int // should also have a clock
}

sig Mailbox {
	mail : Message
}

sig Session {
	sid : one SessionID
}

sig KeyPair {
	privKey : one PrivateKey,
	pubKey : one PublicKey
}

sig PrivateKey {}

sig PublicKey {}

sig DeviceID {}

sig UserID {}

sig SessionID {}

sig Message {
	senderDID : one DeviceID,
	senderUID : one UserID
}

sig UserRecord { // Is this different from User?
	dRecords : DeviceRecord, // at least one???
	stale : Int, // Mark the time this went stale, -1 for active
	knownDevices : PublicKey // For per-user identity keys
}

sig DeviceRecord {
	activeSessions : lone Session,
	inactiveSessions : Session, // should be ordered list here
	stale : Int // Mark the time this went stale, -1 for active
	// known_devices : PublicKey // For per-device identity keys
}

//-----------------------------
// Updating device state
//-----------------------------
pred removeDevice[d,d' : Device, r : DeviceRecord] {
	// precond: r exists in d
	r in d.records.dRecords

	// postcond: 
	// the DeviceRecord is removed. if it is the last DeviceRecord for a given UserRecord, remove that UserRecord as well
	d'.records.dRecords = (d.records.dRecords - r) or 
		some u : UserRecord | d'.records = d.records-u and u in d.records and u.dRecords = {r}
	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime // Should we update time??
}

pred removeUser[d,d' : Device, r : UserRecord] {
	//precond: r exists in d
	r in d.records

	//postcond
	d'.records = d.records - r	

	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime // Should we update time??
}

/* TODO
pred removeSession[d,d' : Device, s : Session] {
	let ss = d.records.drecords.activeSessions + d.records.drecords.inactiveSessions
	// precond: s exists in d
	s in ss

	// postcond: 
	// the Session is removed. if it is the last Session for a given DeviceRecord, remove that DeviceRecord as well
	d'.records.drecords.activeSessions = (d.records.drecords - r) or 
		some u : UserRecord | d'.records = d.records-u and u in d.records and u.drecords = {r}
	// frame conditions
	d'.selfRec = d.selfRec
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime // Should we update time??
}
*/

