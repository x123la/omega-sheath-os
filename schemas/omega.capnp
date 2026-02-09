@0x934efea7f017fff0;

struct Event {
  eventId  @0 :UInt64;  # u128 split? Cap'n Proto UInt64 is max. might need 2 fields or Data.
  # Using Data for u128 to be safe, or 2x UInt64. Let's use 2x UInt64 for u128.
  eventIdLow  @1 :UInt64;
  eventIdHigh @2 :UInt64;
  
  nodeId   @3 :UInt32;
  streamId @4 :UInt16;
  lamport  @5 :UInt64;
  
  # Dependencies
  deps     @6 :List(UInt64); # Simplifying to list of IDs (low bits?) or list of EventRef?
  
  payload  @7 :Data;
  payloadHash @8 :Data; # [u8; 32]
}

struct Certificate {
  certIdLow   @0 :UInt64;
  certIdHigh  @1 :UInt64;
  
  certType    @2 :CertType;
  enum CertType {
    merge @0;
    obstruction @1;
  }
  
  traceRootHash @3 :Data;
  batchId       @4 :UInt64;
  signature     @5 :Data;
  prevCertHash  @6 :Data;
  
  # Body union?
  body :union {
    mergeBody @7 :MergeBody;
    obstructionBody @8 :ObstructionBody;
  }
}

struct MergeBody {
  mergedStateHash @0 :Data;
  acceptedCount   @1 :UInt32;
  witnessHash     @2 :Data;
}

struct ObstructionBody {
  conflictSetLen @0 :UInt16;
  violatedPredicateId @1 :UInt32;
  witnessHash @2 :Data;
  conflictingPayloadHashes @3 :List(Data);
}
