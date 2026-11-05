import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Funnel

/-!
# All-argument envelope on ratio arms

No separate Wald event needed in this dictionary. Use psi per Hot endpoint,
since those h on expansion require accesses at exponentiation. Address
budgets per END OF ALL arms, no distinct-label recycling. η linear even
on full lift. Joint integral inputs reassemble on intact gamma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y : ℝ} {L : Side}
variable (X : Coat T F)
lemma colorless (θ : Rotator P L η r Q Y X) (i j : Tubular f G) (h : ¬ X.Hot i.1 ∨ ¬ X.Hot j.1) :
    X.shreds i j=0 := by
  unfold shreds Window.flawed frameMean
  obtain ⟨u,v,H,-⟩ := θ.room.accepted.feeds
  let A := X.plate; let V := X.relating
  change (A*V-1) i j=0; rw [Matrix.sub_apply,Matrix.mul_apply]; apply sub_eq_zero.mpr
  rcases h with hi|hj
  · have he : A i=(1:Matrix ..) i := funext fun j => X.asleep i hi H j
    rw [show ∑ k,A i k*V k j=((1:Matrix (Tubular f G) (Tubular f G) ℝ)*V) i j by rw [Matrix.mul_apply]; simp_rw [he],one_mul]
    exact X.uniform θ.scale θ.room.accepted _ _ hi
  have he k : V k j=(1:Matrix ..) k j := by
    have ht : V.transpose=V := by rw [← show Vᴴ=V.transpose from by ext; simp]; exact Window.twin ..
    rw [show V k j=V j k from congr_fun (congr_fun ht j) k]; unfold V; rw [X.uniform θ.scale θ.room.accepted j k hj]
    simp only [Matrix.one_apply,eq_comm]
  rw [show ∑ k,A i k*V k j=(A*(1:Matrix (Tubular f G) (Tubular f G) ℝ)) i j by rw [Matrix.mul_apply]; simp_rw [he],mul_one]
  rw [show A i j=A j i from congr_fun (congr_fun X.toned _) _]; unfold A; rw [X.asleep j hj H]; simp only [Matrix.one_apply,eq_comm]

lemma calm (θ : Rotator P L η r Q Y X) (β : ℝ) (i : Tubular f G) (h : ¬ X.Hot i.1) : X.hatted β i=0 := by
  obtain ⟨u,v,H,-⟩ := θ.room.accepted.feeds
  have he : (X.plate *ᵥ X.driftM) i=0 := by
    rw [show (X.plate *ᵥ X.driftM) i=((1:Matrix (Tubular f G) (Tubular f G) ℝ)*ᵥ X.driftM) i by
      unfold Matrix.mulVec dotProduct; exact Finset.sum_congr rfl fun j _ => by dsimp only; rw [X.asleep i h H], Matrix.one_mulVec]; exact X.not_e θ.scale θ.room.accepted _ h
  unfold hatted; rw [Pi.smul_apply,Pi.add_apply,X.no_b i h θ.room.accepted,he]; simp

private lemma single_pair (θ : Rotator P L η r Q Y X) (k : ℕ) (v : Bond f) (p : Itinerary f (k+2))
    (h : combo v p (X.finale k) ≠ 0) : X.Hot v ∧ X.Hot (arrive v p) := by
  induction k generalizing v with
  | zero =>
    let j := Itinerary.next p
    let i := Itinerary.next (after p)
    have hx : combo v p (X.finale 0)= Pulse.Itinerary.restrict (-X.shreds) v j*(Pulse.Itinerary.restrict X.plate j i) := by
      rw [combo,combo,combo]; simp [finale,j,i]
    rw [hx] at h
    have ha := left_ne_zero_of_mul h; have hb := right_ne_zero_of_mul h
    have hi : X.Hot v ∧ X.Hot j := by
      have ht := not_or.mp (show ¬ (¬X.Hot v ∨ ¬X.Hot j) from by
        intro he; apply ha; ext x y
        change (-X.shreds) (v,x) (j,y)=0
        rw [Matrix.neg_apply, X.colorless θ (v,x) (j,y) he, neg_zero])
      exact ⟨not_not.mp ht.1,not_not.mp ht.2⟩
    refine ⟨hi.1,?_⟩
    change X.Hot i
    by_contra ht
    apply hb
    obtain ⟨u,w,hp,-⟩ := θ.room.accepted.feeds
    ext x y
    change X.plate (j,x) (i,y)=0; rw [show X.plate (j,x) (i,y)=X.plate (i,y) (j,x) from congr_fun (congr_fun X.toned _) _,
      X.asleep (i,y) ht hp]
    simp [show i≠j from fun H => ht (H.symm ▸ hi.2)]
  | succ n ih =>
    rw [combo] at h
    have ha := left_ne_zero_of_mul h; have hb := right_ne_zero_of_mul h
    have he : (fun k : ℕ => X.finale (n+1) (k+1))=X.finale n := by funext k; simp [finale]
    rw [he] at hb
    refine ⟨?_, (ih _ (after p) hb).2⟩
    by_contra hx; apply ha; ext x y
    change X.finale (n+1) 0 (v,x) (_,y)=_
    rw [finale,if_pos (by omega), Matrix.neg_apply,X.colorless θ (v,x) _ (Or.inl hx),neg_zero]; rfl

lemma emitting (θ : Rotator P L η r Q Y X) (z : Air f G) (p : Ledger f 2) (h : X.qunique z p ≠ 0) :
    X.Hot p.2.1 ∧ X.Hot (arrive p.2.1 p.2.2) := by
  rcases p with ⟨n,v,l⟩; refine single_pair X θ n v l ?_; intro he
  apply h; unfold qunique circle; dsimp only; rw [he]; simp

section upper
variable (z : Air f G) {β a d i : ℝ} (hβ : 0<β)

def muRate (K a : ℝ) := 4*a+K

def heat (a K : ℝ) (t β : ℝ) := (gStep β)⁻¹*t*(muRate K a)

lemma held {K : ℝ} (hβ : 0<β) (hk : 0<a*X.t) (i : Bond f) (h : X.Hot i) (hn : X.aperture β z a i≠0)
    (he : ‖X.μ i‖ ≤ K*X.t) : ‖X.atmos z i‖ ≤ heat a K X.t β := by
  rw [aperture,if_pos h] at hn
  have hp := X.amount (a:=2*a) (by rw [mul_assoc]; positivity) (X.liftA β z) i hn
  simp only [liftA,Pi.add_apply,Pi.smul_apply] at hp
  let g := gStep β; have hx : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hz : g * ‖X.atmos z i‖ ≤ 2*(2*a)*X.t + K*X.t := by
    have he' := norm_sub_le (X.μ i+g • X.atmos z i) (X.μ i); rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hx.le] at he'
    exact he'.trans (add_le_add hp he)
  apply le_of_mul_le_mul_left _ hx; apply hz.trans_eq; change _ = g*(g⁻¹*X.t*(4*a+K)); field_simp; ring

lemma first_cost (hβ : 0<β) (hk : 0<a*X.t) (θ : Rotator P L η r Q Y X)
    {K U M : ℝ} (hU : 0≤U) (he : heat a K X.t β ≤ U) (hh : 0≤M) (hi : ∀ i,|X.hatted β i| ≤ M)
    (hf : ∀ i,‖X.μ i‖ ≤ K*X.t) (i : Bond f) : |X.qfirst β z a i| ≤ Fintype.card G.ColorIndex * (U*M) := by
  unfold qfirst
  have hz : 0≤ (Fintype.card G.ColorIndex:ℝ)*(U*M) := by positivity
  by_cases hp : X.Hot i
  swap
  · have ht : X.qlinear β z i=0 := sum_eq_zero fun j _ => by rw [X.calm θ β (i,j) hp,mul_zero]
    rw [ht,mul_zero,abs_zero]; exact hz
  by_cases hw : X.aperture β z a i=0
  · rw [hw,zero_mul,abs_zero]; exact hz
  have ht := X.held z hβ hk i hp hw (hf i)
  rw [aperture, if_pos hp,abs_mul,abs_of_nonneg (X.booked ..).1]
  apply (mul_le_of_le_one_left (abs_nonneg _) (X.booked ..).2).trans
  refine ((abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (s:=univ) (f:=fun j : G.ColorIndex => |z (i,j)*X.hatted β (i,j)|)
    (g:=fun _ => U*M) fun j _ => by rw [abs_mul]; exact mul_le_mul ((stand_cap j (X.atmos z i)).trans (ht.trans he)) (hi _) (abs_nonneg _) hU)).trans_eq ?_
  rw [sum_const, nsmul_eq_mul,card_univ]
end upper
end Coat
end YM.ConnectedActivityE6
