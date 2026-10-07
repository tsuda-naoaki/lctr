theory Native_Metadata_01_059
imports
  "LCTR_Core_Finite_Partitions_Alignment.Core_Finite_Partitions_Alignment"
begin
ML_file "../../ReadNativeMetadata.ML"
ML \<open>LCTR_Native_Metadata.emit @{theory} [
  "Core_Finite_Partitions_Alignment.bounded_extensionality",
  "Core_Finite_Partitions_Alignment.classification_bijective",
  "Core_Finite_Partitions_Alignment.classification_on_generator",
  "Core_Finite_Partitions_Alignment.empty_sequence",
  "Core_Finite_Partitions_Alignment.first_failure_components_disjoint",
  "Core_Finite_Partitions_Alignment.first_failure_partition",
  "Core_Finite_Partitions_Alignment.first_failure_sets",
  "Core_Finite_Partitions_Alignment.first_failure_unique",
  "Core_Finite_Partitions_Alignment.injection_is_necessary",
  "Core_Finite_Partitions_Alignment.minimum_index",
  "Core_Finite_Partitions_Alignment.omitted_prefix_not_unique",
  "Core_Finite_Partitions_Alignment.tagged_card",
  "Core_Finite_Partitions_Alignment.tagged_finite",
  "Core_Finite_Partitions_Alignment.tagged_partition"
]\<close>
end
