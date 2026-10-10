theory Native_Metadata_01_173
imports
  "LCTR_Tagged_Lifts_Alignment.Tagged_Lifts_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Tagged_Lifts_Alignment.alignment_equal_value_different_tags",
  "Tagged_Lifts_Alignment.alignment_partialLift_both_identities",
  "Tagged_Lifts_Alignment.alignment_partialLift_inverse",
  "Tagged_Lifts_Alignment.alignment_partialLift_inverse_value",
  "Tagged_Lifts_Alignment.alignment_partialLift_value",
  "Tagged_Lifts_Alignment.alignment_tagLift_composition",
  "Tagged_Lifts_Alignment.alignment_tagLift_injective",
  "Tagged_Lifts_Alignment.alignment_tagLift_inverse",
  "Tagged_Lifts_Alignment.alignment_tagLift_left_inverse",
  "Tagged_Lifts_Alignment.alignment_tagLift_right_inverse",
  "Tagged_Lifts_Alignment.alignment_tagLift_value"
]\<close>
end
