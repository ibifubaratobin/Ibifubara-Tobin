/*

G20735820 CarPark class for Dafny Assignment 2

*/

//using autocontracts so that Valid predicate is added to pre and post conditions
class {:autocontracts} CarPark{
    const capacity : int := 10; //capacity of non-reserved car park
    const rCapacity : int := 10; //capacity of reserved car park
    const weekendCapacity : int := 20; //total cap of carpark as on weekend all spaces are available as non-reserved
    var nrArea : set<int>; //non-reserved car park represented as a set so there are no duplicates
    var rArea : set<int>; // reserved car park also a set so no duplicates
    var subs: set<int>; //set to hold the car id when making reservation 
    const fullSpaceMargin: int := 5; //non-reserved car park considered full when 5 spaces left
    var isWeekend: bool; //will determine if it is a weekend day or not as car park behaves different on weekend
    constructor() //constructor sets up a new car park
    ensures nrArea == {} //ensuring that the non-reserved area is an empty set
    ensures rArea == {} // ensuring that the reserved area is an empty set
    ensures subs == {} //ensuring that the subscriptions are empty
    ensures capacity > 0; //capacity of the nonreserved area has to be greater than 0 after constrcutor is called
    ensures rCapacity > 0; //reserved cap should alos be greater than 0
    ensures isWeekend == false //its not the weekend unless open reserved area is called, so need to set isWeekend to false for now
    {
        rArea := {};
        nrArea := {};
        isWeekend := false;
        subs := {};
    }

    predicate Valid() //predicate set for all the pre and post conditions
    reads this
    {
        //the amount of cars in the non-reserved area must be less than or equal to the capacity of the non-reserved car park
        //minus an extra 5 spaces due to the fact that the car park factors 5 spaces lost because of bad parking
        //also
        //the reserved area size in cars must be less than or equal to the capacity of the reserved area
        (|nrArea| <= capacity - fullSpaceMargin) && (|rArea| <= rCapacity)
    }

    method EnterCarPark(carId : int) //called to enter the non-reserved car park
    requires carId !in nrArea //the carId passed as a parameter needs to be unique and not already in the set
    requires carId !in rArea //the carId passed as a parameter needs to be unique and not already in the set
    requires |nrArea| < capacity - fullSpaceMargin; //the size of the non-reserve area has to be less than the capacity and an extra 5 spaces as the carpark is considered full when 5 spaces are left
    modifies `nrArea //modifying the non-reserve area so need to add a modifies clause
    ensures nrArea == old(nrArea) + {carId} //when the method is done need to ensure that the non-reserve area has the same values as the previous area plus the extra inserted value
    ensures rArea == old(rArea) //ensuring that reserved area hasnt been changed
    ensures subs == old(subs) //ensuring that the subs havent been changed by this method
    ensures |nrArea| > 0 //ensuring that the size of the non-reserved area is greater than 0 after this method has been called
    ensures isWeekend == old(isWeekend) //ensuring that isWeekend hasnt been changed by this method
    {
        //adding the carId to the non-reserved area
        nrArea := nrArea + {carId};
    }

    method LeaveCarPark(carId : int) //this method removes a carId from the set it is stored in, the carId is passed as a parameter
    requires |nrArea| > 0 || |rArea| > 0 //the non-reserved area or the reserved area need to have a carId stored in them in order to be able to remove one
    requires carId in nrArea || carId in rArea //the carId that is passed as a paramete has to exist in either the reserved or non-reserved areas
    modifies `nrArea, `rArea //this method will modify the non-reserved and reserved areas by removing a car from one so need to specify them in the modifies clause
    ensures nrArea == old(nrArea) - {carId} //ensuring that the non-reserved area after the method call is the same as it was before but without the carId that left
    //ensures rArea == old(rArea) - {carId} //ensuring that the reserved area after the method call is the same as it was before but without the carId that left
    ensures subs == old(subs) //ensuring that the subscriptions have not been changed after this call is made
    {
        //removing the carId from the set that it is in
        //if(carId in nrArea){
            nrArea := nrArea - {carId};
        //}else if(carId in rArea){
            rArea := rArea - {carId};
        //}
    }

    method CheckAvailability() //method provided to print the availability of the non-reserved car park --- on weekend this is 20 non-reserved spaces and on weekday it is 10 non-reserved spaces
    modifies this
    ensures nrArea == old(nrArea) //need to ensure that nothing was changed during this method call as otherwise will get pre-condition errors for methods called after this method is called
    ensures rArea == old(rArea)
    ensures isWeekend == old(isWeekend)
    ensures subs == old(subs)
    {
        print "Current Non-reserved Availability: ";
        //if its the weekend the entire car park is non-reserved so need to have a different output for it
        if(isWeekend){
            print weekendCapacity - (|rArea| + |nrArea|);
        }else{
            //not the weekend so just show the output for the weekday
            print capacity - |nrArea|;
        }
        print "\n";
    }

    method EnterReservedCarPark(carId: int) //method to enter the reserved area of the car park, just like the entercarpark method this takes the carId as a parameter
    requires carId !in nrArea //the cardId must not already be in the non-reserved area
    requires carId !in rArea //the carId must not already be in the reserved area
    requires |rArea| < rCapacity //the size of the reserved area must be less than the capacity of the reserved area
    requires carId in subs || isWeekend == true //have to make sure that the carId is either subscribed (weekdays) or it is the weekend which means any car can enter
    modifies this //modifying the reserved area set so need to add the modifies clause
    ensures nrArea == old(nrArea) //ensuring that the non-reserved area has not been changed by this method call
    ensures rArea == old(rArea) + {carId} //ensuring that the reserved area now is the same as the previous set but with an extra carId in it
    ensures subs == old(subs) //ensuring subs has not been changed
    ensures isWeekend == old(isWeekend) //ensuring that the isWeekend boolean has not been changed by this method call
    ensures |rArea| > 0 //ensures that the size of the reserved area is greater than 0 as when a value is added it cant be 0
    {
        //adding the carId to the reserved area
        rArea := rArea + {carId};
    }

    method MakeSubscription(carId: int) //method to add a carId to the subscription list (cars need to be subscribed to park into the reserved area on weekdays) takes carId as a parameter
    requires carId !in subs //need to make sure that the carId is not already in the subscriptions as cars with a sub shouldnt be added again
    modifies this //modifying the subs so need to add the modifies clause
    ensures nrArea == old(nrArea) //ensuring that the non-reserved area is not changed by this method
    ensures rArea == old(rArea) //ensuring that the reserved area is not changed by this method call
    ensures isWeekend == old(isWeekend) //ensuring that the isWeekend boolean is not changed by this method call
    ensures subs == old(subs) + {carId} //ensuring that the subs set has all the values from before including the newly added value
    {
        //adding the carId to the subs set
        subs := subs + {carId};
    }

    method OpenReservedArea() //open reserved area method to open the second barrier on weekends as all the carpark becomes non-reserved
    requires isWeekend == false //should only be able to open the reserved area if it is closed so isWeekend needs to be false when this method is called
    modifies this //modifying the value of the isWeekend boolean so need to add the modifies clause
    ensures isWeekend == true //when this method is called need ensure that isWeekend is now true
    ensures nrArea == old(nrArea) //non-reserved area should stay unchanged
    ensures rArea == old(rArea) //reserved area should stay unchanged
    ensures subs == old(subs) //the subs set should stay unchanged
    {
        //making isWeekend true to indicate it is the weekend
        isWeekend := true;
    }

    method CloseCarPark() //close car park method crushes any cars left in there at the closing time
    modifies this //modifying the values of non-reserved, reserved and isWeekend so need to add modifies clause
    ensures rArea == {} //the reserved area needs to be empty after this method is called
    ensures nrArea == {} //the non-reserved area needs to be empty after this method is called
    ensures subs == old(subs) //subs stay unchanged as sub has been paid for
    ensures isWeekend == false //it could be a weekday after the carpark is closed so need to make sure is weekend is set to false
    {
        nrArea := {};
        rArea := {};
        isWeekend := false;
    }

    method PrintParkingPlan() //extra method to print the car park and subs
    modifies this
    ensures isWeekend == old(isWeekend) //everything should be unchanged as this method doesnt change anything
    ensures nrArea == old(nrArea)
    ensures rArea == old(rArea)
    ensures subs == old(subs)
    {
        //print all of the sets
        print "\n\n";
        print "------------------------------------\n";
        print "|            PARKING PLAN          |\n";
        print "------------------------------------\n";
        print "Subscriptions: ";
        print subs;
        print "\n";
        print "Non-reserved area: ";
        print nrArea;
        print "\n";
        print "Reserved Area: ";
        print rArea;
        print "\n";
        print "------------------------------------\n";
        print "\n";
    }
}

method Main(){
    var cp := new CarPark();

    /* TESTING A WEEKDAY */
    print "\n\n###########  WEEKDAY PARKING  ############\n";

    cp.PrintParkingPlan(); //printing the parking plan should show empty for subs, non-reserved and reserved area

    //cp.LeaveCarPark(1); -- precondition doesnt hold as the carpark is empty so a car cant leave if it is empty

    cp.CheckAvailability(); //non-reserved area car park is 10 capacity, this should print 10
    cp.EnterCarPark(1); //car is entering car park
    cp.CheckAvailability(); //this should now print 9 since a space has been taken

    //cp.EnterReservedCarPark(8); -- pre-condition doesnt hold as its a weekday and the car is not subscribed so cant enter the reserved car park

    cp.MakeSubscription(8); //now making subscription
    cp.MakeSubscription(9); //adding another sub

    //cp.MakeSubscription(8); -- pre-condition doesnt hold as the carId 8 already exists in the subs set

    cp.EnterReservedCarPark(8); //now the subscribed cars can enter the reserved car park as they are subscribed
    cp.EnterReservedCarPark(9);

    cp.PrintParkingPlan(); //printing parking plan should show subs and cars parked in which area

    cp.CloseCarPark(); //weekday finished so close and crush remaining cars (Assignment brief says car park closes every evening at 11pm)

    /* WEEKDAY IS FINISHED */



    /* TESTING WEEKEND */

    print "\n\n ############   WEEKEND PARKING  ############\n";

    cp.PrintParkingPlan(); //printing parking plan for the weekend reserved and non-reserve areas should be empty except for subs since they are monthly
    cp.OpenReservedArea(); //opening the reserved area as it is a weekend day
    cp.CheckAvailability(); //should print 20 as all of the carpark is now non-reserved

    cp.EnterCarPark(15); //cars should still be able to enter non-reserved area of car park
    cp.EnterCarPark(16); //entering another car

    //cars should be able to enter reserved area without subscribing since its weekend
    cp.EnterReservedCarPark(2);
    cp.EnterReservedCarPark(3);
    cp.EnterReservedCarPark(4);

    cp.PrintParkingPlan(); //prints parking plan, car park should include the 5 cars that were just added
    cp.CheckAvailability(); //should print 15 as car park has 5 cars and its weekend so non-reserved capacity is now 20

    cp.LeaveCarPark(3); //car 3 leaves carpark
    cp.LeaveCarPark(15); //car 15 leaves carpark

    cp.PrintParkingPlan(); //car park should now show 3 cars parked inside it
    cp.CheckAvailability(); //availability should increase as 2 cars leave so should print 17

    cp.CloseCarPark(); //closing the car park for the day and crush cars
    cp.PrintParkingPlan();//should show empty car park but subscriptions should still have the subs from before
    cp.CheckAvailability(); //should show 10 again until OpenReservedArea is called again
    /* WEEKEND IS FINISHED */
}
