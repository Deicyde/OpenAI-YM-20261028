import YM.AnalyticNext.QUARTIC_MATCH.Radius.Gradient
import YM.Progress.JOINT_CALENDAR.Issue


/-!
# One post-length chart controls every actual patch branch simultaneously

Work on fixed auxiliary mesh big enough for this purpose. Don't assume that
one choice suffices across its preimages; prove tags agree for every choice on
the original mesh, no minimum formula continuation in large field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

namespace Model
section lists
variable (P : Patch)
def attends := Finset.univ.biUnion (fun i : P.Points × P.Points × Lattice.Order => (visits i.1.val (route i.1.val i.2.1.val i.2.2)).toFinset)
def consults := Finset.univ.biUnion (fun i : P.Points × Axis => (visits i.1.val (List.replicate P.L.val (posDir i.2))).toFinset)
def atEase := attends P ∪ consults P ∪ (Finset.univ.biUnion (fun j : Axis=> (attends P).image (fun i => i+P.L.val • step j)))

def capacity : ℕ := (atEase P).sup size

private theorem needed : ∃ A : Side, 2*capacity P+1 ≤ A.val :=
  ⟨⟨2*capacity P+1,by omega⟩,le_refl _⟩
def marker : Side := (needed P).choose
abbrev native := marker P*P.L
lemma short (x : Cover) (i : Axis) : (x i).natAbs ≤ size x := Finset.single_le_sum (f:=fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
lemma fits (i : Cover) (h : i∈atEase P) : size i ≤ capacity P := Finset.le_sup h
lemma trips (x : Cover) (h : x∈atEase P) (i : Axis) : -( (native P).val : ℤ) < 2*x i ∧ 2*x i ≤ (native P).val := by
  have hb := (short x i).trans (fits P _ h)
  have ht : 2*capacity P+1 ≤ (native P).val := (needed P).choose_spec.trans (Nat.le_mul_of_pos_right _ P.L.property)
  omega
lemma entire (x : Cover) (h : x∈atEase P) : lift (wrap (native P) x) = x := by
  apply wrap_injOn (native P) ?_ (trips P _ h) (wrap_lift _)
  exact lift_centers _
lemma attending (x : Cover) (h : x ∈ attends P) : x ∈ atEase P := Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
lemma consult (x : Cover) (h : x ∈ consults P) : x ∈ atEase P := Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h)))
lemma ease (i : Axis) (x : Cover) (h : x∈attends P) : x + P.L.val • step i ∈atEase P := Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
  ⟨i,Finset.mem_univ i,Finset.mem_image.mpr ⟨x,h,rfl⟩⟩))

variable {G : Gauge} {U V : CoverConfig G}
def near (U V : CoverConfig G) := ∀ (x : Cover) (i : Axis), x∈attends P → U (x,i)=V (x,i)
lemma near_route (h : near P U V) (o x : P.Points) (l : Lattice.Order) : travel U o.val (route o.val x.val l) = travel V o.val (route o.val x.val l) :=
    travel_local o.val (route o.val x.val l) _ _ fun i hi _ => h i.1 i.2 (Finset.mem_biUnion.mpr ⟨(o,x,l),Finset.mem_univ _,List.mem_toFinset.mpr hi⟩)
lemma near_clear (h : near P U V) (K : KernelChoices) : P.usesMin K U ↔ P.usesMin K V := by
  simp_rw [Patch.usesMin,Patch.via,Patch.axial, near_route P h]
lemma near_price (h : near P U V) (f : P.Frame G) : P.score U f=P.score V f := by
  simp_rw [Patch.score,Patch.via, near_route P h]
lemma nearby (h : near P U V) (K : KernelChoices) (hk : P.Branches K G) (he : P.usesMin K V) (p q : P.FrameTag) :
    P.usesMin K U ∧ P.frame K U p=P.frame K V q := by
  have hh := (near_clear P h K).mpr he
  refine ⟨hh,?_⟩; rw [Patch.frame, if_pos hh, Patch.frame,if_pos he]
  refine (hk.frame_unique V he).unique ?_ (P.min_exists V).choose_spec
  obtain ⟨ha,hb⟩ := (P.min_exists U).choose_spec; unfold Patch.selected
  unfold Patch.minimizing; simp_rw [← near_price P h]; exact ⟨ha,hb⟩
end lists
section links
variable {c f : Side} {G : Gauge} (S : StepData c f)
local notation "P" => S.patch
local notation "t" => stepAt P S.kernel (marker P)

def pick (x : Site c) : Dir G f →L[ℝ] Dir G (native P) :=
    ContinuousLinearMap.pi (fun i : Body 1 (native P) => if lift i.1∈atEase P then ContinuousLinearMap.proj (R:=ℝ) (wrap f (lift i.1)+S.ratio.embed x,i.2)
      else 0 )
lemma looks (e : Site c) (x : Cover) (hx : x∈atEase P) (a : Dir G f) (i : TypeFace 1) :
    pick S e a (wrap (native P) x,i) = a (wrap f x + S.ratio.embed e,i) := by
  rw [pick, ContinuousLinearMap.pi_apply]; simp only [entire P x hx,hx,if_true]; rfl
lemma token (e : Site c) (a : Dir G f) (z C : ℝ) (h : trials G z (S.ratio.embed e) a C) (he : 0 ≤ z) (hp : 0≤C) :
    ‖pick S e a‖ ≤ Real.exp (z*capacity P)*C := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [pick,ContinuousLinearMap.pi_apply]; split
  · next hz =>
      apply (h (wrap f (lift i.1)+S.ratio.embed e,i.2)).trans; rw [mul_comm C]; apply mul_le_mul_of_nonneg_right _ hp
      apply Real.exp_monotone; gcongr
      change separation _ _ ≤ _; rw [separation,add_sub_cancel_right]; exact (within_size ..).trans (fits P _ hz)
  rw [_root_.zero_apply,norm_zero]; positivity
lemma fits_token (e : Site c) (a : Dir G f) : ‖pick S e a‖ ≤ ‖a‖ := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using token S e a 0 ‖a‖ (Amount.constant 0 le_rfl _ a) le_rfl (norm_nonneg _)

variable {θ : RG.StepData c f} (u : S.Choices)
def pref (z : Edge (Site c)) := (z.1+step z.2:Site c)
abbrev stamp (C : Patch) (i : Axis) : Edge (Site (marker C)) := (0,i)
lemma travels (e : Edge (Site c)) (a : Dir G f) (x i) (h : x∈atEase P) :
    expandAt (S.ratio.embed e.1) (represent a) (x,i)= expandAt ((t).ratio.embed 0) (represent (pick S e.1 a)) (x,i) := by
  unfold expandAt; rw [represent_link, represent_link]
  dsimp only; rw [show (t).ratio.embed 0=0 from map_zero (t).ratio.root,add_zero, looks S e.1 x h]
lemma moves (e : Edge (Site c)) (a : Dir G f) :
    near P (expandAt (S.ratio.embed (pref e)) (represent a)) (expandAt ((t).ratio.embed (pref (stamp P e.2))) (represent (pick S e.1 a))) := by
  intro x i hx; unfold expandAt; rw [represent_link,represent_link]; dsimp only
  obtain ⟨y,j⟩ := e; dsimp only [pref,stamp]
  have hb := ease P j x hx
  rw [Ratio.embed_leap,Ratio.embed_leap, show (t).ratio.embed 0=0 from map_zero (t).ratio.root,zero_add, ← wrap_step (native P), ← map_nsmul, ← map_add]
  change G.lieExp (a (wrap f x+(S.ratio.embed y+(P).L.val • step j),coord i)) = G.lieExp (pick S y a (wrap (native P) (x+(P).L.val • step j),coord i))
  rw [looks S y (x+(P).L.val • step j) hb]; congr 2; rw [map_add,map_nsmul,wrap_step]; abel_nf
lemma compiles (hk : (P).Branches S.kernel G) (e : Edge (Site c)) (a : Dir G f) (u' : (t).Choices)
    (hx : ∀ z : Site (marker P), (t).patch.usesMin S.kernel (Push.product t z (pick S e.1 a))) :
    (P).usesMin S.kernel (Push.product S e.1 a) ∧ S.connector (represent a) u.1 e =
      (t).connector (represent (pick S e.1 a)) u'.1 (stamp P e.2) := by
  let E := pick S e.1 a; let f' := t
  let d := stamp P e.2
  have he : near P (Push.product S e.1 a) (Push.product t (0:Site (marker P)) E) := fun x i h => travels S e a x i (attending P x h)
  obtain ⟨hp,hz⟩ := nearby P he S.kernel hk (hx 0) (u.1 e.1) (u'.1 0)
  have hy := (nearby P (moves S e a) S.kernel hk (hx _) (u.1 (pref e)) (u'.1 (pref d))).2
  have ht v : travel (Push.product S e.1 a) (v:(P).Points).val (List.replicate (P).L.val (posDir e.2)) = travel (Push.product t 0 E) v.val (List.replicate (P).L.val (posDir e.2)) :=
    travel_local v.val (List.replicate (P).L.val (posDir e.2)) _ _ fun i hi _ => travels S e a _ _ (consult P _ (Finset.mem_biUnion.mpr
      ⟨(v,e.2),Finset.mem_univ _,List.mem_toFinset.mpr hi⟩))
  exact ⟨hp,funext fun i => congr_arg₂ (·*·) (congr_arg₂ (·*·) (congr_fun hz i) (ht i)) (congr_arg (·⁻¹) (congr_fun hy i))⟩
end links
end Model
end YM.AnalyticNext.QuarticMatch.Radius
