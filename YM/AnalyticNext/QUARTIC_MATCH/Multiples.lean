import YM.AnalyticNext.QUARTIC_MATCH.Joint
import YM.Bid.Drops
import YM.Work.B06
import YM.Work.E04

/-!
# Testing on period multiples

No divisibility hypotheses on `Schedule.period`. This is a device for proving
periodization; COMPARE via enlargements, not selecting special physical periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Sheets
open Matrix Lattice RG Wilson Tree Precision Exterior Bid Filter Function Topology Joint
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

section fibers
variable {c d : Side} (h : c.val ∣ d.val)

/-- Projection from the covering torus onto the given one. -/
def project : Site d →+ Site c where
  toFun x i := ZMod.castHom h (Per c) (x i)
  map_zero' := by ext; simp
  map_add' x y := funext fun i => map_add _ _ _

lemma project_wrap (x : Cover) : project h (wrap d x) = wrap c x :=
    funext fun i => map_intCast (ZMod.castHom h (Per c)) (x i)
lemma project_on : Surjective (project h) := fun i => ⟨wrap d (lift i),(project_wrap h _).trans (wrap_lift i)⟩
lemma project_signed (s : Signed) (x : Site d) : project h (s.act x)=s.act (project h x) := by
  rw [← wrap_lift x,wrap_signed,project_wrap,project_wrap,wrap_signed]
lemma project_vec (x : Step) : project h (x.vec : Site d) = x.vec := by rw [← wrap_vec, project_wrap,wrap_vec]
lemma project_step (x : Axis) : project h (step x) = step x := project_vec h (posDir x)

abbrev Deck := (project h).ker

-- pin one section

def pin (x : Site c) := (project_on h x).choose
@[simp] lemma pin_site (x : Site c) : project h (pin h x) = x := (project_on h x).choose_spec

def split : Site c × ↥(Deck h) ≃ Site d where
  toFun p := pin h p.1 + p.2.val
  invFun i := (project h i,⟨i-pin h (project h i),by simp⟩)
  left_inv := by
    rintro ⟨i,j⟩; have hx : project h j.val=0 := j.property
    apply Prod.ext <;> simp [hx]
  right_inv := by intro i; dsimp; abel

-- make canonical decidable instance to avoid nondefeq issues
-- (overlap existing AddSubgroup instances; use natCard for factor)
def mult : ℕ := Nat.card (Deck h)
lemma mult_pos : 0 < mult h := Nat.card_pos
lemma cards : Fintype.card (Site c) * mult h = Fintype.card (Site d) := by
  classical
  cases nonempty_fintype (Deck h)
  rw [← Fintype.card_congr (split h), Fintype.card_prod,mult,Nat.card_eq_fintype_card]

@[simp] lemma split_base (x : Site c) (i : Deck h) : project h (split h (x,i))=x := by
  change project h (pin h _ + i.val)=_; rw [map_add,pin_site,show project h i.val=0 from i.property,add_zero]

lemma count_sum {E : Type*} [AddCommMonoid E] (F : Site c → E) : ∑ i : Site d, F (project h i) = mult h • ∑ i,F i := by
  classical
  cases nonempty_fintype (Deck h)
  rw [← Equiv.sum_comp (split h) (fun i => F (project h i)), Fintype.sum_prod_type]
  simp_rw [split_base h,Finset.sum_const,Finset.card_univ,← Finset.smul_sum]; rw [mult,Nat.card_eq_fintype_card]
lemma count_extra {E ι : Type*} [AddCommMonoid E] [Fintype ι] (F : Site c × ι → E) :
    ∑ i : Site d × ι, F (project h i.1,i.2)=mult h • ∑ i : Site c × ι,F i := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; exact count_sum h (fun i => ∑ j,F (i,j))

/-- A deck-translation invariant function is periodic of the smaller size. -/
lemma periodic {E : Type*} (F : Site d → E) (hf : ∀ (u : Site d), project h u=0 → ∀ x, F (x+u)=F x) :
    (F ∘ pin h) ∘ project h = F := by
  funext i
  obtain ⟨⟨x,u⟩,rfl⟩ := (split h).surjective i
  simp only [Function.comp_apply,split_base]
  exact (hf u u.property _).symm

/-- Pull up positive orientations. -/
def copies (U : Config G c) : Config G d := fun e => U (project h e.1,e.2)
def reuses {k : ℕ} : fieldDir G c k →L[ℝ] fieldDir G d k :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (project h i.1,i.2)
def spine : LieSpin G c →L[ℝ] LieSpin G d :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (project h i)
lemma represented (u : Dir G c) : copies h (represent u)=represent (reuses h u) := rfl

lemma pull_copies (s : Signed) (b : Site d) (U : Config G c) :
    pull s b (copies h U) = copies h (pull s (project h b) U) := by
  funext i; unfold copies pull Step.read Step.used; simp only [affine]
  split <;> simp [*,map_add,project_signed h, project_step]
lemma expand_copies (b : Site d) (U : Config G c) : expandAt b (copies h U)=expandAt (project h b) U := by
  funext e; unfold copies expandAt; simp [map_add,project_wrap]
lemma gauge_copies (U : Config G c) (t : Spin G c) :
    Lattice.gauge (t ∘ project h) (copies h U) = copies h (Lattice.gauge t U) := by
  funext i; simp only [Lattice.gauge,copies,Function.comp_apply,map_add,project_step]
lemma face_copy (U : Config G c) (i : Face (Per d)) : faceValue (copies h U) i=faceValue U (project h i.1,i.2) := by
  have he (w : Walk) (b : Site d) : travel (copies h U) b w = travel U (project h b) w := calc
    _ = travel (expandAt b (copies h U)) 0 w := by rw [travel_at,map_zero,zero_add]
    _ = _ := by rw [expand_copies,travel_at,map_zero,zero_add]
  exact he ..
lemma uncut_copy {m : ℕ} (A : ℕ → Atom G m) (U : Config G c) : uncut A (copies h U)=mult h • uncut A U := by
  have he x i : (A i).unmasked (copies h U) x=(A i).unmasked U (project h x) := by
    simp_rw [Atom.unmasked,RG.Slot.atSite,expand_copies h]
  unfold uncut; simp_rw [he]; exact count_sum h fun i => ∑' j,(A j).unmasked U i
lemma quadratic_copy (p : Clip) (W : PathData G) (U : Config G c) : quadratic p W (copies h U)=mult h • quadratic p W U := by
  have he i : W.ell (copies h U) i=W.ell U (project h i.1,i.2) := by
    simp_rw [PathData.ell,PathData.ellTerms, RG.Slot.atSite, expand_copies h]
  unfold quadratic
  simp_rw [he,face_copy]
  exact count_extra h fun i : Face (Per c) => p.direct * G.price (faceValue U i) + ‖W.ell U i‖^2/2
lemma main_copy (p : Clip) (W : PathData G) (U : Config G c) : mainTerm p W (copies h U)=mult h • mainTerm p W U := by
  simp_rw [mainTerm,Patch.average,pull_copies, map_zero, quadratic_copy, uncut_copy, ← smul_add, ← Finset.smul_sum,nsmul_eq_mul]
  ring
lemma wilson_copy (U : Config G c) : energy (copies h U) = mult h • energy U := by
  simp_rw [energy,face_copy]; exact count_extra h fun i : Face (Per c) => G.price (faceValue U i)
end fibers

section lanes
variable (P : Patch) (K : KernelChoices) {c d : Side} (h : c.val∣d.val)

abbrev stepAt (c : Side) := (⟨P,K,rfl⟩ : StepData c (c*P.L))
include h
lemma within : (c*P.L).val ∣ (d*P.L).val := mul_dvd_mul_right h _

lemma multiplicity_eq : mult (within P h)=mult h := by
  have hc := cards (within P h); have ha := cards h
  simp_rw [site_card,PNat.mul_coe,mul_pow] at hc ha
  apply Nat.eq_of_mul_eq_mul_right (show 0<c.val^4*P.L.val^4 by positivity)
  rw [mul_comm,hc]; rw [← ha]; ring

-- embedding by L maps between deck groups
lemma project_embed (x : Site d) : project (within P h) ((stepAt P K d).ratio.embed x)=
    (stepAt P K c).ratio.embed (project h x) := by
  rw [← wrap_lift x]; rw [Ratio.embed_wrap, project_wrap,project_wrap,Ratio.embed_wrap]
  rfl

def embedDeck : Deck h → Deck (within P h) := fun x =>
    ⟨(stepAt P K d).ratio.root x.val,by
      have he : project h x.val=0 := x.property
      change project (within P h) ((stepAt P K d).ratio.embed _) = _
      rw [project_embed P K h, he]; exact (stepAt P K c).ratio.root.map_zero⟩

lemma embedDeck_onto : Surjective (embedDeck P K h) := by
  classical
  letI := Fintype.ofFinite (Deck h); letI := Fintype.ofFinite (Deck (within P h))
  have hh := multiplicity_eq P h; unfold mult at hh; simp only [Nat.card_eq_fintype_card] at hh
  have he : Injective (embedDeck P K h) := fun x y h => Subtype.ext
    ((stepAt P K d).ratio.embed_injective (congr_arg Subtype.val h))
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨he,hh.symm⟩).2

/-- Same tag assigned on repetitions, only for pointwise step comparisons; NO claim that
this lifting maps the measures on tags or predictors. -/
def mimic (t : (stepAt P K c).Choices) : (stepAt P K d).Choices :=
    ⟨t.1 ∘ project h, fun i => t.2 (project h i.1,i.2)⟩
lemma pred_copies (U : Config G (c*P.L)) (t : (stepAt P K c).Choices) :
    (stepAt P K d).prediction (copies (within P h) U) (mimic P K h t) = copies h ((stepAt P K c).prediction U t) := by
  let S := stepAt P K c
  let T := stepAt P K d
  let U' := copies (within P h) U
  let s := mimic P K h t
  have he x : T.frames U' s.1 x=S.frames U t.1 (project h x) := by
    unfold StepData.frames U'; rw [expand_copies,project_embed]; rfl
  funext e
  have hh : T.connector U' s.1 e=S.connector U t.1 (project h e.1,e.2) := by
    funext x
    simp only [StepData.connector,he,U',expand_copies, map_add,project_step]
    rw [show project (within P h) (T.ratio.embed e.1) = _ from project_embed P K h e.1]
  change P.predict K (T.connector _ _ _) _=P.predict K (S.connector _ _ _) _
  rw [hh]; rfl
lemma field_copy (t : (stepAt P K c).Choices) (p : Clip) (W : PathData G)
    (V : Config G c) (U : Config G (c*P.L)) (Φ : Spin G c) :
    fieldAction _ (mimic P K h t) p W (copies h V) (copies (within P h) U) (Φ ∘ project h) =
      mult h • fieldAction (stepAt P K c) t p W V U Φ := by
  simp only [fieldAction, main_copy, multiplicity_eq P h, pred_copies, smul_add]
  rw [gauge_copies]
  have he (Y V : Config G c) : groupEnergy K (copies h Y) (copies h V)=mult h • groupEnergy K Y V := by
    unfold groupEnergy
    have hh := count_extra h fun i : Edge (Site c) => G.price (V i * (Y i)⁻¹)
    rw [show (∑ i, G.price (copies h V i * (copies h Y i)⁻¹)) = _ from hh, nsmul_eq_mul, nsmul_eq_mul]; ring
  rw [he]


def ride : Vertical G c (c*P.L) →L[ℝ] Vertical G d (d*P.L) :=
    (reuses (k:=1) (within P h)).prodMap (spine h)

def rideAlong : Dir G c × Vertical G c (c*P.L) →L[ℝ] Dir G d × Vertical G d (d*P.L) :=
    (reuses (k:=1) h).prodMap (ride P h)
lemma action_copy (t : (stepAt P K c).Choices) (p : Clip) (W : PathData G)
    (z : Dir G c × Vertical G c (c*P.L)) :
    Joint.action (stepAt P K d) (mimic P K h t) p W (rideAlong P h z) =
      (mult h:ℝ) * Joint.action (stepAt P K c) t p W z := by
  rw [← nsmul_eq_mul]; exact field_copy P K h t p W (represent z.1) (represent z.2.1) (power z.2.2)
end lanes
end YM.AnalyticNext.QuarticMatch.Sheets
