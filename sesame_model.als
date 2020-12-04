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
pred deleteDevice[d,d' : Device, r : DeviceRecord] {
	// precond: r exists in d
	r in d.records.dRecords

	// postcond: 
	// the DeviceRecord is removed. if it is the last DeviceRecord for a given UserRecord, remove that UserRecord as well
	d'.records.dRecords = (d.records.dRecords - r) or 
		some u : UserRecord | deleteUser[d,d',u] and u.dRecords = {r}
	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime // Should we update time??
}

pred deleteUser[d,d' : Device, r : UserRecord] {
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

pred deleteSession[d,d' : Device, s : Session] {
	let ss = d.records.dRecords.activeSessions + d.records.dRecords.inactiveSessions | {

	// precond: s is some session in d
	s in ss

	// postcond: 
	// the Session is removed. if it is the last Session for a given DeviceRecord, remove that DeviceRecord as well
	d'.records.dRecords.activeSessions = (d.records.dRecords.activeSessions - s) or 
	d'.records.dRecords.inactiveSessions = (d.records.dRecords.inactiveSessions - s) or
		some r : DeviceRecord | deleteDevice[d,d',r] and ss = {s}
	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime // Should we update time??
	}
}

pred insertSession[d,d' : Device, dr,dr' : DeviceRecord, s : Session] {
	//precond:
	// assumption: the session to be inserted didn't exist in that devicerecord's session list already. 
	// ... not specified in spec
	dr' in d'.records.dRecords
	dr in d.records.dRecords
	//postcond:
	dr'.activeSessions = s
	// the old active session gets added to inactiveSessions
	// note: this prevents duplicates in inactiveSessions, which may not be true in spec
	// we don't keep track of ordering of inactiveSessions
	dr'.inactiveSessions = dr.activeSessions + dr.inactiveSessions

	d'.records.dRecords = d.records.dRecords - dr + dr'

	// frame conditions 
	dr'.stale = dr.stale
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime
}

pred activateSession[d,d' : Device, dr,dr' : DeviceRecord, s : Session] {
	// precond
	s in dr.inactiveSessions
	dr in d.records.dRecords
	dr' in d'.records.dRecords

	// postcond
	dr'.activeSessions = s
	// Note: no ordering to inactiveSessions.
	// Remove the activated session, and add the old activated session 
	dr'.inactiveSessions = dr.inactiveSessions - s + dr.activeSessions
	
	d'.records.dRecords = d.records.dRecords - dr + dr'

	// frame conditions
	dr'.stale = dr.stale
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime
}

pred markUserStale[d,d' : Device, ur,ur' : UserRecord] {
	//precond
	ur in d.records
	ur' in d'.records
	
	ur'.knownDevices = ur.knownDevices
	ur'.dRecords = ur.dRecords
	//postcond
	ur'.stale = d.elapsedTime // mark user stale
	
	d'.records = d.records - ur + ur'

	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime
}

pred markDeviceStale[d,d' : Device, dr,dr' : DeviceRecord] {
	//precond
	dr in d.records.dRecords
	dr' in d'.records.dRecords
	
	dr'.activeSessions = dr.activeSessions
	dr'.inactiveSessions = dr.inactiveSessions
	//postcond
	dr'.stale = d.elapsedTime // mark user stale
	
	d'.records.dRecords = d.records.dRecords - dr + dr'

	// frame conditions
	d'.selfRecord = d.selfRecord
	d'.did = d.did
	d'.keys = d.keys
	d'.elapsedTime = d.elapsedTime
}

//todo: conditionally update, prepare for encrypting
