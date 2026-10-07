import CoreContinuumNativeRecords

namespace LCTR.CoreObserverRecordImages
set_option autoImplicit false
open Set LCTR.CoreTrajectoryDescent LCTR.CoreObserverTime
open LCTR.CoreRecordCodes LCTR.CoreContinuumNativeRecords
variable {C D B P N : Type}

abbrev WindowCode (D P N : Type) := Code D (Set D) P N

def codeImage (code : WindowCode D P N) (S : Set D) : Set code.Values :=
  encoded code '' S
def canonicalImage (d : Input C D B) (code : WindowCode D P N) (S : Set D) : Set (Time d) :=
  {t | ∃ v ∈ codeImage code S, (nativeRecords d code id).codeRelation 0 t v}
def orderImage (d : Input C D B) (h : IncTrans d) (code : WindowCode D P N)
    (S : Set D) : Set (OrderTime d h) :=
  orderProjection d h '' canonicalImage d code S
def realImage (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (code : WindowCode D P N) (S : Set D) : Set ℝ :=
  timeRep d h rho '' canonicalImage d code S

theorem code_image_exact (code : WindowCode D P N) (S : Set D) :
    Subtype.val '' codeImage code S = code.value '' S := by
  simp only [codeImage,Set.image_image]
  rfl

theorem canonical_image_relation_inverse (d : Input C D B) (code : WindowCode D P N)
    (S : Set D) (t : Time d) :
    t ∈ canonicalImage d code S ↔ ∃ v ∈ code.value '' S, (t,v) ∈ timeRecords d code := by
  constructor
  · rintro ⟨v,hv,hr⟩
    refine ⟨v.val,?_,(native_time_records d code id t v).mp hr⟩
    rw [← code_image_exact]
    exact ⟨v,hv,rfl⟩
  · rintro ⟨v,⟨r,hr,eq⟩,hv⟩
    refine ⟨encoded code r,⟨r,hr,rfl⟩,?_⟩
    apply (native_time_records d code id t (encoded code r)).mpr
    change (t,code.value r) ∈ timeRecords d code
    exact eq.symm ▸ hv

theorem canonical_image_source_witness (d : Input C D B) (code : WindowCode D P N)
    (S : Set D) (t : Time d) :
    t ∈ canonicalImage d code S ↔
      ∃ w ∈ S, ∃ x : Raw d, timeProjection d x.val.1 = t ∧
        code.value x.val.2.1 = code.value w := by
  constructor
  · rintro ⟨v,⟨w,hw,ev⟩,⟨x,hx,ex⟩⟩
    exact ⟨w,hw,x,hx,congrArg Subtype.val (ex.trans ev.symm)⟩
  · rintro ⟨w,hw,x,hx,eq⟩
    exact ⟨encoded code w,⟨w,hw,rfl⟩,x,hx,Subtype.ext eq⟩

theorem source_record_in_image (d : Input C D B) (code : WindowCode D P N)
    (S : Set D) (c : C) (r : D) (b : B) (src : d.relation c r b) (hr : r ∈ S) :
    timeProjection d c ∈ canonicalImage d code S :=
  (canonical_image_source_witness d code S _).mpr ⟨r,hr,⟨(c,r,b),src⟩,rfl,rfl⟩

theorem equal_code_record_in_image (d : Input C D B) (code : WindowCode D P N)
    (S : Set D) (c : C) (r w : D) (b : B) (src : d.relation c r b)
    (hw : w ∈ S) (eq : code.value r = code.value w) :
    timeProjection d c ∈ canonicalImage d code S :=
  (canonical_image_source_witness d code S _).mpr ⟨w,hw,⟨(c,r,b),src⟩,rfl,eq⟩

theorem injective_code_window_characterization (d : Input C D B) (code : WindowCode D P N)
    (inj : Function.Injective code.value) (S : Set D) (t : Time d) :
    t ∈ canonicalImage d code S ↔
      ∃ x : Raw d, x.val.2.1 ∈ S ∧ timeProjection d x.val.1 = t := by
  rw [canonical_image_source_witness]
  constructor
  · rintro ⟨w,hw,x,hx,eq⟩
    exact ⟨x,(inj eq).symm ▸ hw,hx⟩
  · rintro ⟨x,hs,hx⟩
    exact ⟨x.val.2.1,hs,x,hx,rfl⟩

theorem image_monotonicity (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (code : WindowCode D P N) {S T : Set D} (sub : S ⊆ T) :
    codeImage code S ⊆ codeImage code T ∧
    canonicalImage d code S ⊆ canonicalImage d code T ∧
    orderImage d h code S ⊆ orderImage d h code T ∧
    realImage d h rho code S ⊆ realImage d h rho code T := by
  have hc : codeImage code S ⊆ codeImage code T := Set.image_mono sub
  have ht : canonicalImage d code S ⊆ canonicalImage d code T := by
    rintro t ⟨v,hv,hr⟩
    exact ⟨v,hc hv,hr⟩
  exact ⟨hc,ht,Set.image_mono ht,Set.image_mono ht⟩

theorem equal_code_images_same_time_images (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) (code : WindowCode D P N) {S T : Set D}
    (eq : codeImage code S = codeImage code T) :
    canonicalImage d code S = canonicalImage d code T ∧
    orderImage d h code S = orderImage d h code T ∧
    realImage d h rho code S = realImage d h rho code T := by
  have e : canonicalImage d code S = canonicalImage d code T := by
    unfold canonicalImage
    rw [eq]
  exact ⟨e,congrArg (fun A => orderProjection d h '' A) e,
    congrArg (fun A => timeRep d h rho '' A) e⟩

theorem real_image_factorization (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) (code : WindowCode D P N) (S : Set D) :
    realImage d h rho code S = rho.value '' orderImage d h code S := by
  unfold realImage orderImage timeRep
  rw [Set.image_image]
  rfl

theorem real_image_membership (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) (code : WindowCode D P N) (S : Set D) (z : ℝ) :
    z ∈ realImage d h rho code S ↔
      ∃ w ∈ S, ∃ x : Raw d, code.value x.val.2.1 = code.value w ∧
        timeRep d h rho (timeProjection d x.val.1) = z := by
  constructor
  · rintro ⟨t,ht,hz⟩
    obtain ⟨w,hw,x,hx,eq⟩ := (canonical_image_source_witness d code S t).mp ht
    exact ⟨w,hw,x,eq,(congrArg (timeRep d h rho) hx).trans hz⟩
  · rintro ⟨w,hw,x,eq,hz⟩
    exact ⟨timeProjection d x.val.1,
      (canonical_image_source_witness d code S _).mpr ⟨w,hw,x,rfl,eq⟩,hz⟩

theorem nonempty_images (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (code : WindowCode D P N) (S : Set D) :
    (realImage d h rho code S).Nonempty ↔ (canonicalImage d code S).Nonempty := by
  exact Set.image_nonempty

theorem empty_window_images (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (code : WindowCode D P N) :
    codeImage code ∅ = ∅ ∧ canonicalImage d code ∅ = ∅ ∧
    orderImage d h code ∅ = ∅ ∧ realImage d h rho code ∅ = ∅ := by
  simp [codeImage,canonicalImage,orderImage,realImage]

theorem four_images_unique (d : Input C D B) (h : IncTrans d) (rho : RealEmbedding d h)
    (code : WindowCode D P N) (S : Set D) :
    ∃! images : Set code.Values × Set (Time d) × Set (OrderTime d h) × Set ℝ,
      images.1 = codeImage code S ∧
      images.2.1 = {t | ∃ v ∈ images.1, (nativeRecords d code id).codeRelation 0 t v} ∧
      images.2.2.1 = orderProjection d h '' images.2.1 ∧
      images.2.2.2 = rho.value '' images.2.2.1 := by
  refine ⟨(codeImage code S,canonicalImage d code S,orderImage d h code S,realImage d h rho code S),
    ⟨rfl,rfl,rfl,real_image_factorization d h rho code S⟩,?_⟩
  rintro ⟨a,b,c,e⟩ ⟨ha,hb,hc,he⟩
  dsimp at ha hb hc he
  subst a
  subst b
  subst c
  subst e
  exact congrArg (fun z => (codeImage code S,canonicalImage d code S,
    orderImage d h code S,z)) (real_image_factorization d h rho code S).symm

theorem native_record_cell_factorization (d : Input C D B) (h : IncTrans d)
    (rho : RealEmbedding d h) (code : WindowCode D P N) (r : D) :
    realImage d h rho code (code.window r) =
      rho.value '' orderImage d h code (code.window r) :=
  real_image_factorization d h rho code (code.window r)

end LCTR.CoreObserverRecordImages
