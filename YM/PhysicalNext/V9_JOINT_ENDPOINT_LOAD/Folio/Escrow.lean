import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Lit

/-! # Rank money lives in the topology of the whole component and the individual awards

Decompose `totalBill` with same bills/footprint at all exposures. Repeated
stops *inside* long ordered products aren't necessarily counted by cover
numbers; their polynomial price escapes into that individual address's hit
norm instead. No suppression withdrawal to pay the number of ratio terms.
$/g$ (actual incoming beta, not bare station `betaHat`) terms must be paid
by the right t and t' before iterating -- not g^{-k} per ordinary component.
Uses output cover convention B = radiusB betaHat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading Tariff
open MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {Q : Kiosk} {k n : ℕ} {θ E : ℝ} {d : Desk G S} {u : Spot d}
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
    {H R ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
    {X : Support c} {l : Viewport u X H R ι} {D : u.Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {s : Seats l z} {M : Income α β γ (H⊕R)} {o : Site c} {j : ℕ} {N : ℝ}

def depthCost (s : Seats l z) := ∏ i:s.big,(1+steps (s.issued i):ℝ)

omit [Fintype α] [Fintype β] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] in
lemma depth_earns (s : Seats l z) : 1≤depthCost s ∧ ∀ i:s.big,(1+steps (s.issued i):ℝ)≤depthCost s := by
  have h (i : s.big) : 1 ≤ (1+steps (s.issued i):ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  refine ⟨Finset.one_le_prod fun i _ => h i,fun i=> ?_⟩
  simpa [depthCost,fun j => max_eq_left (h j)] using Finset.le_prod_max_one (Finset.mem_univ i) (fun i:s.big => (1+steps (s.issued i):ℝ))

structure Vault (d : Desk G S) (Q : Kiosk) (k j : ℕ) (N : ℝ) : Prop where
  thirty : 30 ≤ N
  rank : (1+k:ℝ) ≤ N
  booth : ((j*(4*k):ℕ):ℝ) ≤ N
  reach : (1+radiusB d.betaHat:ℝ) ≤ N
  projected : ((S.patch.L.val^4*Fintype.card Axis:ℕ):ℝ)≤N
  colors : (Fintype.card G.ColorIndex:ℝ)≤ N
  growth : |Q.v.price|≤N
  pays : 0 < Q.cap ∧ 8*Q.cap ≤ N
  base : 1 + backFactor G ≤ N
  dims : G.colorScale ≤ N
  toll b : 1 + ‖Notice.term G b‖ * |Q.L| ≤ N
  kinetic : max 1 ‖d.g⁻¹‖ * d.out.threshold ≤ N ∧ ‖d.g⁻¹‖*fiery G d.betaHat S.patch.L≤N

structure Escrow (X : Support c) (M : Income α β γ (H⊕R)) (d : Desk G S) (Q : Kiosk) (k j : ℕ) (N : ℝ) : Prop extends Vault d Q k j N where
  plan : max 1 M.plan ≤ j
  letters : (Fintype.card α:ℝ) ≤ N ∧ (Fintype.card β:ℝ) ≤ N ∧ (Fintype.card γ:ℝ) ≤ N
  township : (coverNumber (radiusB d.betaHat) X:ℝ) ≤ N
  margins : |M.royalty| ≤ N
  other : ∑ i, M.wages i ≤ N

namespace Vault
lemma big (h : Vault d Q k j N) : 1 ≤ N := (by norm_num : (1:ℝ) ≤ 30).trans h.thirty
end Vault
namespace Escrow
variable (h : Escrow X M d Q k j N)
include h
omit [DecidableEq β] [DecidableEq γ] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma pace (i o : Site c) (hi : i∈X) (ho : o∈X) : 1+(separation i o:ℝ) ≤ N^3 := by
  let v := radiusB d.betaHat
  have ht : (separation i o:ℝ) ≤ coverNumber v X * (4*v+2:ℝ) + 2*v := by exact_mod_cast (Corona.extent X v hi ho)
  have hb := h.reach
  have hv := h.township
  have hw := h.thirty
  have he : 4*(v:ℝ)+2≤4*N := by unfold v; linarith only [hb]
  have hy := mul_le_mul hv he (by positivity) (show 0≤N by linarith only [hw])
  unfold v at ht; unfold v at hy
  nlinarith only [ht,hy,hb,hw]


omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq H] [DecidableEq R] h in
private lemma crowd (l : Viewport u X H R ι) : Fintype.card (H⊕R) ≤ Viewport.frameCost S X := by
  let f (i : H⊕R) := ((⟨home S (l.edges i),l.activePos i (Set.mem_insert ..)⟩:X), S.ratio.residue (l.edges i).1,(l.edges i).2)
  have hf : Injective f := by
    intro i j he; apply l.read.injective; apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · have hp := congr_arg (fun z => (z.1 : ↥X).val) he
      have hr := congr_arg Prod.fst (congr_arg Prod.snd he)
      change (l.edges i).1=(l.edges j).1
      rw [← S.ratio.unpack_at (l.edges i).1,← S.ratio.unpack_at (l.edges j).1]
      change home S (l.edges i) = home S (l.edges j) at hp
      unfold home at hp
      change S.ratio.residue (l.edges i).1 = S.ratio.residue (l.edges j).1 at hr
      rw [hp,hr]
    exact (show (f i).2.2=(f j).2.2 from congr_arg _ (congr_arg Prod.snd he))
  have ht := Fintype.card_le_of_injective f hf
  change _ ≤ Fintype.card ((↥X) × Site S.ratio.count × Axis) at ht
  simp only [Fintype.card_prod, Fintype.card_coe, Lattice.site_card, ← mul_assoc] at ht; exact ht

omit [DecidableEq β] [DecidableEq γ] [DecidableEq H] [DecidableEq R] in
lemma size (l : Viewport u X H R ι) : max (Fintype.card H:ℝ) (max (Fintype.card (H×G.ColorIndex):ℝ) (Fintype.card (Component G H R):ℝ)) ≤ N^10 := by
  have hb := h.reach; let v := radiusB d.betaHat; have hw := h.thirty
  have hz : 0 ≤ N := by linarith
  have hX : (X.card:ℝ) ≤ N^8 := calc
    _ ≤ coverNumber v X*(v+v+1:ℝ)^4 := by exact_mod_cast (Corona.pays X v)
    _ ≤ N*(2*N)^4 := by gcongr; exact h.township; unfold v; linarith only [hb]
    _ ≤ _ := by
      calc N*(2*N)^4 ≤ N^6 := by ring_nf; exact mul_le_mul_of_nonneg_left (show (16:ℝ)≤N by linarith) (by positivity : 0 ≤ N^5) |>.trans_eq (by ring)
           _ ≤ _ := pow_le_pow_right₀ h.big (by decide)
  have hP : (Fintype.card (H⊕R):ℝ) ≤ N^9 := calc
    _ ≤ (Viewport.frameCost S X:ℝ) := by exact_mod_cast crowd l
    _ ≤ _ := by
      unfold Viewport.frameCost; rw [Nat.mul_assoc,Nat.cast_mul, pow_succ N 8]
      gcongr; exact h.projected
  have hQ : (Fintype.card H:ℝ) ≤ N^9 := by
    rw [Fintype.card_sum,Nat.cast_add] at hP; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card R)]
  have hh := h.colors
  have hY {u : Type} [Fintype u] (hf : (Fintype.card u:ℝ) ≤ N^9) : (Fintype.card (u × G.ColorIndex):ℝ) ≤ N^10 := by rw [pow_succ,Fintype.card_prod,Nat.cast_mul]; gcongr
  exact max_le (hQ.trans (pow_le_pow_right₀ h.big (by decide))) (max_le (hY hQ) (hY hP))

def locale (s : Seats l z) := ∀ i:s.big, ∀ x∈clues (s.issued i), site x∈X

omit [DecidableEq β] [DecidableEq γ] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma charges (ho : o∈X) (hs : locale s) (q : ℕ) (i : s.big) : s.charge o q i ≤ depthCost s * N^(3*q) := by
  let V := X.sup (fun i => separation i o)
  have hv (i : Site c) (hi : i∈X) : separation i o ≤ V := Finset.le_sup (s:=X) (f:=fun i=> separation i o) hi
  have hx : 1+(V:ℝ) ≤ N^3 := by
    obtain ⟨i,hi,hV⟩ := Finset.exists_mem_eq_sup X ⟨o,ho⟩ (fun i=>separation i o)
    unfold V; rw [hV]; exact h.pace i o hi ho
  have hw (i : u.ActiveKey) (hi : site i∈X) := hv (site i) hi
  obtain ⟨hN,he⟩ := depth_earns s
  unfold Seats.charge; rw [pow_mul]; generalize ht : s.issued i=p
  have hf := hs i; rw [ht] at hf
  rcases p with a|⟨n,⟨a,b⟩,f⟩
  · apply le_trans (b:=1 * (N^3)^q) _ (mul_le_mul_of_nonneg_right hN (by have := h.big; positivity : 0≤(N^3)^q))
    rw [one_mul]; change grade q o (site a) ≤ _; dsimp only [Sum.elim_inl, grade]; gcongr
    exact h.pace _ _ (hf a (by simp [clues])) ho
  apply (same_cost (o:=o) (k:=q) (n+1) a f |>.le.trans (amount_cost site a f (hw a (hf a (by simp [clues]))) (fun k=> hw _ (hf _ (by simp [clues]))))).trans
  gcongr
  specialize he i; rw [ht] at he; exact (le_trans (b:=1+((n+2:ℕ):ℝ)) (by push_cast; linarith) he)

variable (l)
omit [DecidableEq β] [DecidableEq γ] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma motion (i : H × G.ColorIndex) (ho : o∈X) : |motionBill Q.v l o Q.L k i| ≤ N^(6+3*d.out.power*(k+1)) := by
  have hx := h.thirty; have hy : 0 ≤ N := zero_le_one.trans h.big
  let a := site (l.read (.inl i.1))
  have hv := h.pace a o (l.activePos (Sum.inl i.1) (Set.mem_insert ..)) ho
  let D := 3*d.out.power*(k+1)
  have hd (q) (hq : q ≤ d.out.power*(k+1)) : grade q o a ≤ N^D := by
    unfold grade; exact (pow_le_pow_left₀ (by positivity) hv _).trans ((pow_mul ..).symm.le.trans (pow_le_pow_right₀ h.big (by unfold D; nlinarith)))
  let V := max (1:ℝ) ‖d.g⁻¹‖ * d.out.threshold
  have hV : 0≤V := by unfold V; have hh:=d.out.threshold_pos; positivity
  have hR : 0 ≤ 1+backFactor G := le_of_lt (by unfold backFactor; positivity)
  let z := 1+‖Notice.term G i.2‖ * Q.L
  have hz : |z| ≤ N := by
    have h' := abs_add_le (1:ℝ) (‖Notice.term G i.2‖ * Q.L)
    rw [abs_one,abs_mul,abs_norm] at h'
    exact h'.trans (h.toll i.2)
  have h1 : |V * z * (k+1:ℝ) * (1+backFactor G) * G.colorScale * grade d.out.power o a| ≤ N^5 * N^D := by
    simp only [abs_mul, abs_of_nonneg hV,abs_of_nonneg (show 0 ≤ (k+1:ℝ) by positivity),abs_of_nonneg hR,abs_of_nonneg G.colorScale_pos.le,abs_of_pos (grade_pos ..)]
    have he : ∀ {a b c d e f : ℝ}, 0 ≤ a → 0 ≤ b → 0≤c → 0≤d → 0≤e → 0≤f → a≤N → b≤N → c≤N → d≤N → e≤N → f≤N^D → a*b*c*d*e*f ≤ N^5*N^D := by
      intro a b c d e f _ _ _ _ _ _ _ _ _ _ _ _; rw [show N^5=N*N*N*N*N by ring]; gcongr
    apply he hV (abs_nonneg _) (by positivity) hR G.colorScale_pos.le (grade_pos ..).le h.kinetic.1 hz
      ((add_comm ..).le.trans h.rank) h.base h.dims (hd _ (Nat.le_mul_of_pos_right _ (by omega)))
  have h2 : |1+‖d.g⁻¹‖ * (Q.v.price * fiery G d.betaHat S.patch.L)| ≤ 2*N^2 := by
    apply (abs_add_le ..).trans
    have hf := d.paidScale.le
    rw [abs_one,abs_mul,abs_mul,abs_norm,abs_of_nonneg hf,mul_left_comm]
    have hA := mul_le_mul h.growth h.kinetic.2 (mul_nonneg (norm_nonneg _) hf) hy
    nlinarith only [hA,hx]
  unfold motionBill rung climbing expenditure; unfold Viewport.edges
  rw [show _*(z*((k+1:ℝ)*((1+backFactor G)*(G.colorScale*_))))=V*z*(k+1:ℝ)*(1+backFactor G)*G.colorScale*grade d.out.power o a from ?_]
  swap
  · unfold V grade a site; ring
  refine (abs_add_le ..).trans ((add_le_add h1 (le_trans (c:=2*N^2*N^D) (abs_mul ..).le ?_)).trans ?_)
  · exact mul_le_mul h2 ((abs_of_nonneg (grade_pos ..).le).le.trans (hd (d.out.power*k) (Nat.mul_le_mul_left _ (Nat.le_succ k)))) (abs_nonneg _) (by positivity)
  change N^5*N^D + 2*N^2*N^D ≤ N^(6+D)
  rw [← add_mul,pow_add]
  have h5 := pow_le_pow_right₀ h.big (by decide : 2 ≤ 5)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy _)
  rw [pow_succ N 5]; exact le_trans (b:=N^5 * 3) (by linarith only [h5]) (by gcongr; linarith)
end Escrow
end YM.PhysicalNext.JointLoad.Folio
