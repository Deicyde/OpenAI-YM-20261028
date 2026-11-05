import YM.Next.RANK.Cadence
import YM.Next.RANK.Ratios

/-! # Paid powers and payloads from the lit stamps -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points m} {hk : i≤k} {hi : middle C.path.levels b k ≤ i}
variable {c : Course C N p k}
variable {ξ : Purse}

lemma incomeR1 (w : Purse) (s) : w.ledger s*w.cash s*Perch.bill 1 s ≤ Perch.bill (-6) s:= by
  unfold Purse.ledger Purse.cash Purse.principal; rw [overlap,overlap,overlap]; exact Glimmer.billed _ (by linarith only [w.fits])
lemma incomeR2 (w : Purse) (s) : w.double s*w.cash s^2 * Perch.bill 1 s ≤ Perch.bill (-6) s:= by
  unfold Purse.double Purse.cash; rw [pow_two,overlap,overlap,overlap]; exact Glimmer.billed _ (by linarith only [w.fits])

lemma expend (k' : V→ Ω) (P : Normal.poly V) : coin (rename k' P) ≤ coin P:= by
  rw [Normal.labelled]; refine (Rise.rise _ _ zero_le_one (le_refl 1) (fun i=>?_) P (le_refl _)).trans ?_; swap
  · simp [coin]
  simp
structure Corridor (A : Levels G) (s : ℝ) (p : Purse) (k : ℕ) : Prop where
  heft : Allowed A s k
  races : Racer p (clim A k) (k-middle A s k)
  spend : Faring p (clim A k)
  court i : Station.width A s k ≤ i → i≤k → clim A i∈ Set.Icc (clim A k/2) (clim A k)
structure KFlux (k l : ℕ) (X : AtlasData G C.S p) (V : Purse) (F : Lead G C.S p) : Prop where
  steps j : l≤ j → j<k → Awake (F j) (track X j) V.L (V.sends (clim C.path.levels k))
  color j : l ≤ j → j<k → Voice F j
  realPath j : l ≤ j → j<k → ∀ (m : Chamber G C.S j p → ℝ) i',
    let z:= Normal.reads (F j).H (fun i=>(↑(m i:ℝ):ℂ)) i'
    z=(↑z.re:ℂ)

variable (X : AtlasData G C.S p) (F : Lead G C.S p)
section
variable {P : Rep G (C.side k p)} (W : StampDuty C k N p d ξ.taylor P ξ.era.coast.Q X)
variable (Y : Corridor C.path.levels b ξ k) (v : Fin m→ C.label d)
variable (O : KFlux (C:=C) k (middle C.path.levels b k) X ξ F)
variable (Z : ∀ i, coin (W.W (v i))≤ ξ.principal (clim C.path.levels k))
include Y
lemma foresight (Q : Fin m→ Normal.poly (Chamber G C.S k p)) (hk : i≤k) (hi : middle C.path.levels b k ≤ i)
    (hq : ∀ i, coin (Q i) ≤ ξ.principal (clim C.path.levels k)) (hx : ∀ i,totalDegree (Q i)≤ ξ.taylor)
    (hr : ∀ j, i ≤ j → j<k → (F j).Fair ξ.L) : ∀ u,
    let p:= polygon F Q hk u
    let s:= clim C.path.levels k
    coin p≤ (match u with
      | .inl _=> ξ.ledger s
      | .inr _=> ξ.double s) ∧ totalDegree p≤ 2*ξ.taylor:= by
  let A:=C.path.levels; let ℓ:=middle A b k; let s:=clim A k;let d:=ξ.taylor;let y:=k-i
  have he : y ≤ k-ℓ:= Nat.sub_le_sub_left hi k
  have hx₁ : hike ξ.L d y ≤ Perch.bill 1 s:= le_trans (pow_le_pow_right₀ (pay_crest ξ.loan d) he) Y.races.one
  have hx₂ : hike ξ.L (2*d) y ≤ Perch.bill 1 s:= le_trans (pow_le_pow_right₀ (pay_crest ξ.loan (2*d)) he) Y.races.two
  let L(v: Fin m):= polygon F Q hk (.inl v)
  let B:= ξ.principal s; have hB : 0≤ B:= (Real.exp_pos _).le
  let C:= ξ.ledger s; have hC: 0≤ C:= (Purse.stock_pos ..).le
  have hY (u: Fin m): coin (L u)≤ C ∧ totalDegree (L u)≤ d:= by
    obtain ⟨ht,hf⟩:=flying F _ hk ξ.loan hr (hx u); exact ⟨ht.trans (mul_le_mul (hq u) hx₁ (ample ξ.L _ _ ξ.loan) hB),hf⟩
  rintro (u|v)
  · change coin (L u)≤C ∧ totalDegree (L u) ≤ _
    obtain ⟨hw,hP⟩:= hY u; exact ⟨hw,hP.trans (Nat.le_mul_of_pos_left d (by norm_num))⟩
  let u:=v.val.1;let w:=v.val.2;let D:= Q u*Q w;let p:=twoRoot F Q hk v
  have hd : totalDegree D ≤ 2*d:= le_trans (totalDegree_mul ..) (le_trans (add_le_add (hx u) (hx w)) (by unfold d;omega))
  have hD : coin D ≤ B^2:= (Rise.funds _ zero_le_one ..).trans ((mul_le_mul (hq u) (hq w) (Rise.sign _ _ zero_le_one) hB).trans_eq (pow_two ..).symm)
  obtain ⟨hu,h₁⟩:= hY u; obtain ⟨hz,h₂⟩:= hY w; obtain ⟨hh,hw⟩:=flying F _ hk ξ.loan hr hd
  let U:= L u*L w
  change coin (p-U)≤ ξ.double s ∧ _
  refine ⟨(tricolor ..).trans ((add_le_add (hh.trans (mul_le_mul hD hx₂ (ample ξ.L _ _ ξ.loan) (sq_nonneg B))) ((funds _ zero_le_one ..).trans (le_trans (mul_le_mul hu hz (Rise.sign _ _ zero_le_one) hC) (pow_two ..).symm.le))).trans Y.races.cone),?_⟩
  change totalDegree (p-U)≤2*d; rw [sub_eq_add_neg,show -U=(-1:ℂ) • U by simp]; exact (totalDegree_add ..).trans (max_le hw ((totalDegree_smul_le ..).trans ((totalDegree_mul ..).trans (le_trans (add_le_add h₁ h₂) (by omega)))))

include Z O
lemma vertex_cap (i) (hk : i≤k) (x : Points m) (h : middle C.path.levels b k ≤ i) u :
    let P:= jacketPol (F:=F) (s:=b) x v W hk u
    let s:=clim C.path.levels k
    coin P≤ (match u with
      | .inl _=> ξ.ledger s
      | .inr _=> ξ.double s) ∧ totalDegree P ≤ 2*ξ.taylor:= by
  let s:=clim C.path.levels k; let f j:= prefaced W (v j) (Station.choose C.path.levels b k x j)
  have hf i:coin (f i)≤ ξ.principal s:= le_trans (expend ..) (le_trans (expend ..) (Z i))
  have hY i: totalDegree (f i) ≤ ξ.taylor:= (totalDegree_rename_le ..).trans ((totalDegree_rename_le ..).trans (W.duration _))
  exact foresight (b:=b) F Y f hk h hf hY (fun j hj H=> (O.steps _ (h.trans hj) H).pay) u

variable (i : ℕ) {Q : Rep G (C.side i p)} (R : ReadySh (A:=C.path.levels) b X ξ.horizon ξ.era.coast.Q k F) (x : Points m)
variable (hk : i≤k) (h : middle C.path.levels b k ≤ i) (c : Course C N p k)

end
end YM.Next.Rank.Tapes
