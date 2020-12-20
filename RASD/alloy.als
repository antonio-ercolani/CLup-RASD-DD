abstract sig Customer{
ticket: one Ticket
}


--CLup user
sig RegisteredUser extends Customer{
meansOfTranportation: lone Transportation,
visits: set Visit,
position: lone Position
}

--Normal customers, non CLup user
sig InPresenceCustomer extends Customer{
}

sig Date{}

sig QrCode{}

abstract sig Ticket{
number: one Int,
code: QrCode,
store: Store
}

--ticket created by the system
sig VirtualTicket extends Ticket{}

--ticket released by the ticket machine
sig PhysicalTicket extends Ticket{}

--booked visit
sig Visit{
date: Date,
itemsToBuy: set Item,
store: Store
}

--store item
sig Item {
quantity: one Int
} {
quantity > 0
}

sig Transportation {}

--opening days
sig Timetable {
opening: some Date
}

--store queue
sig Queue{
inLine: set Customer,
length: one Int,
interfaces: some TicketMachine
} {
length>=0
}

sig Store{
name: set String,
queue: Queue,
capacity: one Int,
insideCustomers: set Customer,
timetable: Timetable,
location: one Position
} {
capacity > 0
}

sig StoreManager {
supervises: Store
}

sig Position{}

sig TicketMachine{
emittedTickets: set PhysicalTicket
}



//FACTS

--a customer cannot interact (i.e. queueing or being inside) two different stores at the same time
fact UbiquityConstraint1 {
all customer: Customer | all disj s1,s2: Store | 
(customer in s1.insideCustomers or customer in s1.queue.inLine) implies 
not (customer in s2.insideCustomers or customer in s2.queue.inLine)
}

--a user cannot have two booked visits in the same date
fact UbiquityConstraint2{
all user: RegisteredUser | all v1, v2: Visit |
(v1 != v2 and v1 in user.visits) implies not(v2 in user.visits and v1.date = v2.date)
}


--a customer cannot be both inside the store and in the queue
fact UbiquityConstraint3{
all store: Store | all customer: Customer |
customer in store.insideCustomers implies
not (customer in store.queue.inLine)
}


--ticket consistency
fact TicketLogic {
all customer: Customer | all t: Ticket |
(t in customer.ticket) implies (customer in t.store.insideCustomers or 
customer in t.store.queue.inLine)
}


--physical tickets are emitted only by ticketmachines and the store for which the ticket is
--valid is the store whose ticket machine belongs
fact PhysicalTicketConsistency{
all ticket: PhysicalTicket | one ticketMachine: TicketMachine, s :Store |
ticket in ticketMachine.emittedTickets and s in ticket.store and
ticketMachine in s.queue.interfaces
}


fact PhysicalTicketConsistency2{
all customer: InPresenceCustomer | one ticketMachine: TicketMachine |
customer.ticket in ticketMachine.emittedTickets
}


--QrCodes are unique
fact UniqueQrCode {
no disj t1,t2: Ticket | t1.code = t2.code
}


--visit belongs to only one user
fact OneOwnerForVisit{
all visit: Visit | one user: RegisteredUser |
visit in user.visits
}


--every ticket belongs to a customer
fact OneOwnerForTicket{
all t: Ticket | one customer: Customer |
t in customer.ticket
}


fact {
all item: Item | some visit: Visit |
item in visit.itemsToBuy
}


fact {
all transportation: Transportation | some user: RegisteredUser |
transportation in user.meansOfTranportation
}


fact {
all t: Timetable | one store: Store |
t in store.timetable
}


fact {
all d: Date | some visit: Visit |
d in visit.date
}


--no visits can be booked when the store is not open
fact OpeningHours{
all visit: Visit, s: Store |
(s in visit.store) implies (visit.date in s.timetable.opening)
}


--no one is in queue if there is residual capacity in the store
fact QueueLogic {
all store: Store | 
(#store.insideCustomers < store.capacity) implies
(#store.queue.length = 0)
}


--a store cannot exceed his capacity limit
fact CapacityConstraint {
no store: Store | #store.insideCustomers > store.capacity
}


fact QueueLength{
all queue: Queue | #queue.inLine = queue.length
}


--Ticket Machines belong to one queue, and consequently store, at a time
fact TicketMachineConsistency{
no ticketMachine: TicketMachine | some q1, q2: Queue | 
q1 != q2 and ticketMachine in q1.interfaces and
ticketMachine in q2.interfaces
}


fact TicketMachineConsistency2{
all ticketMachine: TicketMachine | one queue: Queue |
ticketMachine in queue.interfaces 
}


--every queue belongs to one store only
fact {
all q: Queue | one store: Store |
q in store.queue
}




//ASSERTIONS

assert QueueConsistency{
no store: Store |
#store.queue.length > 0 and #store.insideCustomers < store.capacity
}
check QueueConsistency


assert LegalLimit {
no store: Store |
#store.insideCustomers > store.capacity
}
check LegalLimit


assert OneStoreAtTime {
no customer: Customer | all s1,s2: Store |
(s1 != s2 and (customer in s1.insideCustomers or customer in s1.queue.inLine)) and
(customer in s2.insideCustomers or customer in s2.queue.inLine)
}
check OneStoreAtTime


assert TicketValidity {
no ticket: Ticket | all s: Store |
s not in ticket.store and ticket in s.queue.interfaces.emittedTickets
} 
check TicketValidity




pred OneStore {
#RegisteredUser > 1 
#InPresenceCustomer > 1
#Transportation < 2
#Item < 2
#Store = 1
#TicketMachine < 3
}

run OneStore for 5


pred TwoStores {
#RegisteredUser > 1 
#InPresenceCustomer > 1
#Transportation < 2
#Store = 2
#TicketMachine < 3
#Visit < 2
}

run TwoStores for 5


