import YM.Next.SCHEDULE.Continuing
import YM.Next.SCHEDULE.Resize
import YM.Next.SCHEDULE.TensorCost


/-!
# Path atom transfer costs through actual covers

Test stationarity `Bounds` and the cost of calling VStep with such paths.
No fixed path or finite-length assumption. Account for all root-stencil
halo charges from Projection via same support functions proved earlier. Fuses
the actual LEFT ordered derivatives with that shape and contracted path-width
rate. No proof here that large Gaussian histories permit these estimates;
specific operation conditional on those inputs and thresholds fit post-L.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Wages
open Work.G07 Lattice RG Wilson Finset Corona
open scoped Matrix.Norms.Frobenius ContDiff BigOperators Topology
variable {G : Gauge} {n : Side} {k : ℕ}

private lemma routes (l : Walk) (x : Cover) (o : Site n) : ∃ f : ℕ → Site n,f 0 = wrap n x+o ∧
    (∀ i<l.length,separation (f i) (f (i+1)) ≤ 1) ∧ ∀ y ∈ visits x l,∃ i ≤ l.length,wrap n y + o=f i := by
  induction l generalizing x with
  | nil => exact ⟨fun _ => _,rfl,fun i hi => by simp at hi,by simp [visits]⟩
  | cons a l ih =>
    obtain ⟨R,hR,ht,h⟩:=ih (x+a.vec)
    let F : ℕ → Site n
      | 0 => wrap n x+o
      | i+1 => R i
    refine ⟨F,rfl,?_,fun y hy => ?_⟩
    · rintro (_|i) hi
      · change separation _ (R 0) ≤ 1
        rw [hR,map_add,wrap_vec,separation_translate,separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]
        split
        · rw [pdist_neg]; apply pdist_step
        apply pdist_step
      apply ht i
      simp at hi; omega
    rcases List.mem_cons.mp hy with h'|h'
    · exact ⟨0,Nat.zero_le _,h' ▸ rfl⟩
    obtain ⟨i,hi,H⟩:=h _ h'; exact ⟨i+1,Nat.add_le_add_right hi _,H⟩

private lemma visitsCost (x : Cover) (l : Walk) (o : Site n) (M : ℕ) (hm : 0 < M) :
    M*coverNumber M ((visits x l).toFinset.image (fun x => wrap n x + o)) ≤ M+l.length := by
  obtain ⟨f,hf,hr,hg⟩:=routes l x o
  obtain ⟨D,H,hD,Hh⟩:=itinerary f _ M hr hm
  rw [Nat.add_comm]; apply le_trans _ hD; apply Nat.mul_le_mul_left M
  apply Corona.list_cost; constructor
  · intro i hi
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hi; obtain ⟨v,hV,hh⟩:=hg y (List.mem_toFinset.mp hy); rw [hh]; exact Hh _ hV
  refine Corona.ship_halo _ fun i hi j hj => Relation.ReflTransGen.mono ?_ i j (H _ hi _ hj)
  rintro i j ⟨a,b,c⟩; exact ⟨a,b,c.trans (by omega)⟩

private lemma first_visit (x : Cover) (l : Walk) : x ∈ visits x l := by cases l <;> simp [visits]
private lemma stop_visit (x : Cover) (l : Walk) : stop x l ∈ visits x l := by induction l generalizing x <;> simp_all [visits,stop]

def walkCuts (s : Slot) (o : Site n) := s.stencil.image fun x=>wrap n x+o

private lemma stays (s : Slot) (o : Site n) : o ∈ walkCuts s o := mem_image.mpr
  ⟨0,mem_union_left _ (List.mem_toFinset.mpr (first_visit _ _)),by simp⟩

lemma walked (s : Slot) (o : Site n) (M : ℕ) (hp : 0<M) :
    M*coverNumber M (walkCuts s o) ≤ 2*M+s.length := by
  let l := square s.plaq.val.1 s.plaq.val.2
  let F x := wrap n x+o
  unfold walkCuts Slot.stencil; rw [image_union]
  have hx : F s.offset∈(visits 0 s.walk).toFinset.image F :=
    mem_image_of_mem _ (List.mem_toFinset.mpr (stop_visit _ _))
  have hy : F s.offset∈(visits s.offset l).toFinset.image F :=
    mem_image_of_mem _ (List.mem_toFinset.mpr (first_visit _ _))
  apply le_trans (Nat.mul_le_mul_left M (Corona.meets_sum hx hy M))
  rw [Nat.mul_add]
  apply le_trans (Nat.add_le_add (visitsCost _ _ o M hp) (visitsCost _ _ o M hp))
  change M+s.walk.length+(M+4) ≤ 2*M+(s.walk.length+4); omega

theorem traversed (a : Atom G k) (o : Site n) (M : ℕ) (hp : 0 < M) :
    M * coverNumber M (a.footprint o) ≤ M+(k*(2*M)+a.length) := by
  let s i := walkCuts (a.leg i) o
  have ht (l : Finset (Fin k)) : M*coverNumber M (insert o (l.biUnion s)) ≤ M+(l.card*(2*M)+∑ i∈l,(a.leg i).length) := by
    induction l using Finset.induction_on with
    | empty =>
      simp only [biUnion_empty,insert_empty_eq,card_empty,zero_mul,sum_empty,Nat.add_zero]
      have hh : coverNumber M ({o}:Support n) ≤ ({o}:Support n).card := by
        refine Corona.list_cost M ⟨halo_subset M {o}, Corona.ship_halo _ ?_⟩
        intro i hi j hj; rw [mem_singleton.mp hi,mem_singleton.mp hj]
      calc
        _ ≤ _ := Nat.mul_le_mul_left _ hh
        _ ≤ _ := by simp
    | @insert i v hi ih =>
      rw [card_insert_of_notMem hi,biUnion_insert]
      have he : insert o (s i ∪ v.biUnion s) = (insert o (v.biUnion s)) ∪ s i := by ext; simp; aesop
      rw [he]
      apply le_trans (Nat.mul_le_mul_left M (Corona.meets_sum (mem_insert_self ..) (stays (a.leg i) o) M))
      rw [Nat.mul_add,sum_insert hi,Nat.add_mul,Nat.one_mul]
      exact le_trans (Nat.add_le_add ih (walked (a.leg i) o M hp)) (by omega)
  have h := ht Finset.univ
  unfold Atom.footprint Atom.stencil Atom.length
  simpa [s,walkCuts,image_insert,biUnion_image] using h

/-- Keep a spare chunk of true path exponent (e.g. to get enhanced
smallness from declared long paths) in addition to charging output cover
exponents. -/
def toll (b : BudgetPoint) (σ : ℝ) (a : Atom G k) : ℝ := Real.exp ((σ/4)*a.length)*price b a

-- plus moment bill paid once with given `σ`.
def fund (G : Gauge) (P i k : ℕ) (A σ : ℝ) : ℝ :=
    startup G k P i * Real.exp (A*(1+2*(k:ℝ))) * momentCost (grade k P i) σ

lemma ticket (b : BudgetPoint) (σ C : ℝ) (hσ : 0 < σ) (hM : b.supportExponent / b.B ≤ σ/4)
    (F : ℕ → Atom G k) (hs : SumBudget (fun i => (F i).budget σ) C) (o : Site n) :
    SumBudget (fun i => b.mass ((F i).footprint o) (toll b σ (F i)))
      (fund G b.power b.order k b.supportExponent σ * b.threshold^k * C) := by
  let d := grade k b.power b.order; let t:= momentCost d σ
  let U:= startup G k b.power b.order; let e := b.supportExponent*(1+2*(k:ℝ))
  have hU : 0≤U := by unfold U startup; have hh:=lt_of_lt_of_le zero_lt_one (slot_ge G b.power b.order 0); positivity
  have hp := decay_summable d (σ/4) (by positivity)
  have ht :0≤t:=tsum_nonneg (fun i => show 0≤decay d _ i by unfold decay; positivity)
  let K := fund G b.power b.order k b.supportExponent σ * b.threshold^k
  have hh := b.threshold_pos
  have hk : 0 ≤ K := by change 0≤U*Real.exp e*t*_; positivity
  have hv (i) := hp.sum_le_tsum ({i}:Finset ℕ) (fun i _ => by unfold decay; positivity)
  refine smaller (f:=fun i => K*(F i).budget σ) ⟨fun i=>mul_nonneg hk (hs.1 i), hs.2.1.mul_left K, by
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hs.2.2 hk⟩ (fun i => ?_) le_rfl
  let l := (F i).length; let H:=coverNumber b.B ((F i).footprint o)
  have hl := traversed (F i) o b.B b.B_pos
  have hE : b.supportExponent * H ≤ e+σ/4*l := by
    unfold e
    have hb : 0 < (b.B:ℝ) := Nat.cast_pos.mpr b.B_pos
    have hA : (b.B:ℝ)*↑H ≤ b.B+((k:ℝ)*(2*b.B)+(l:ℝ)):=by unfold H l; exact_mod_cast hl
    have hE : (H:ℝ) ≤ (1+2*k:ℝ)+(l:ℝ)/b.B := by
      field_simp; linarith
    have hc := mul_le_mul_of_nonneg_left hE b.exponent_pos.le
    have hd := mul_le_mul_of_nonneg_right hM (show 0≤(l:ℝ) by positivity)
    apply hc.trans; rw [mul_add]; apply add_le_add_right
    convert hd using 1; ring
  have hm : decay d (σ/4) l ≤ t := by simpa only [sum_singleton,t,momentCost] using hv l
  let w := (F i).magnitude; have hw : 0≤w := by unfold w Atom.magnitude; positivity
  rw [BudgetPoint.mass,toll,scan]
  change 0≤Real.exp (b.supportExponent*H)*(Real.exp _*(U*b.threshold^k*w*((l:ℝ)+1)^d)) ∧ _
  refine ⟨by positivity,?_⟩
  let Y:=U*b.threshold^k*w
  have hP := Real.exp_pos e
  have HX : Real.exp (b.supportExponent*H+(σ/4)*l) ≤ Real.exp e * Real.exp (σ*l)*Real.exp (-(σ/4)*l) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_monotone; nlinarith only [hE,hσ,Nat.cast_nonneg (α:=ℝ) l]
  calc
    _ = Real.exp (b.supportExponent*H+(σ/4)*l)*((l:ℝ)+1)^d*Y := by rw [Real.exp_add]; unfold H Y d U w l; ring
    _ ≤ Real.exp e*Real.exp (σ*l) * decay d (σ/4) l*Y := by
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HX (by positivity)) (by unfold Y;positivity))
      unfold decay; apply le_of_eq; ring
    _ ≤ Real.exp e*Real.exp (σ*l)* t*Y := by unfold Y; gcongr
    _ = _ := by change _ = (U*Real.exp e*t*b.threshold^k)*(w*Real.exp (σ*l)); unfold Y; ring



variable {s : Survey G} {q : Quote} {e : Exchange} {j i : ℕ}

end YM.Next.Scheduling.Wages
