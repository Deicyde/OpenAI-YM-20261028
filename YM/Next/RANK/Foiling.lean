import YM.Next.RANK.StagePass

/-! # Cost of all wind tests at the middle stop -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {c : Course C N p k} {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}
variable (F : MarketGrant c P X R ξ)

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable {x : Points m} (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (v : Fin m→ C.label d) (Z : ∀ i, coin (O.W (v i))≤ ξ.principal (clim C.path.levels k))

-- seeded costs; compare at full finances. Need same Warp.

def fault1 (s : ℝ) (p : Purse) := p.principal s* knox s * knox s * p.sends s
def fault2 (s : ℝ) (p : Purse) := p.principal s ^2 * knox s * knox s * p.sends s

def fault (s : ℝ) (p : Purse) := fault1 s p+ fault2 s p + 2* p.ledger s * fault1 s p

include H F Z
lemma occasion (x : Points m) (i : pennant m) :
    let h:= before C.path.levels ξ.band k
    let p₀:= jacketPol (F:=R) (s:=ξ.band) x v O h i
    let v':= jacketPol (F:=track X) (s:=ξ.band) x v O h i
    let u:= p₀-v'
    u.totalDegree ≤ 2*ξ.taylor ∧ coin u ≤ fault (clim C.path.levels k) ξ:= by
  intro h p₀ v' u; let A:= C.path.levels; let s:= clim A k; let Y:= fun i=> prefaced O (v i) (Station.choose A ξ.band k x i); let ℓ:=middle A ξ.band k
  let q:= ξ.ledger s; let L:=knox s; let b:=ξ.principal s; let y:= k-ℓ; let D:=ξ.taylor
  have hx:0≤L:= (Real.exp_pos _).le; have hy:0 ≤ ξ.sends s:= (Real.exp_pos _).le
  have ht:0 ≤ b:= (Real.exp_pos _).le; have hq:0 ≤ q:= mul_nonneg ht hx
  let W:= polygon R Y h; let E:=polygon (track X) Y h
  have hf i:coin (Y i)≤ ξ.principal s:= le_trans (expend ..) (le_trans (expend ..) (Z i))
  have hY i: totalDegree (Y i) ≤ ξ.taylor:= (totalDegree_rename_le ..).trans ((totalDegree_rename_le ..).trans (O.duration _))
  have hW:= foresight R H Y h le_rfl hf hY (fun i hi h=> (F.probes.steps i hi h).pay)
  have hE:= foresight (track X) H Y h le_rfl hf hY (fun i hi h=> (F.probes.steps i hi h).cut)
  constructor
  · change totalDegree (p₀-v')≤_
    rw [sub_eq_add_neg,show -v'=(-1:ℂ)•v' by simp]; refine (totalDegree_add ..).trans (max_le (hW _|>.2) ((totalDegree_smul_le ..).trans (hE _|>.2)))
  let f := fault1 s ξ; let g:=fault2 s ξ
  have he' (P c) (n : ℕ) (h₁ : totalDegree P ≤ n) (h₂ : coin P≤c) (h₃ : hike ξ.L n y ≤ knox s) : coin (shelve R h P - shelve (track X) h P) ≤ c* L* L*ξ.sends s := by
    apply (diminish R _ h ξ.loan hy (track X) F.probes.steps h₁).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h₂ h₃ (ample _ _ _ ξ.loan) ((Rise.sign _ _ zero_le_one).trans h₂)) H.races.family (Nat.cast_nonneg (α:=ℝ) y) (mul_nonneg ((Rise.sign _ _ zero_le_one).trans h₂) hx)) hy
  change coin (W i-E i)≤_
  have hp i:coin (W (.inl i)- E (.inl i))≤f:= he' _ b D (hY i) (hf i) H.races.one
  cases i with
  | inl i=>
    refine (hp i).trans ?_; change f≤ f+g+2*q*f
    have hh:0≤f:= (Rise.sign _ _ zero_le_one).trans (hp i); have ht:0 ≤ g:= mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hx) hx) hy; linarith only [ht,mul_nonneg hq hh]
  | inr i=>
    let j:=i.val.1; let u:=i.val.2; let Y':=Y j*Y u
    have hu:totalDegree Y'≤2*D:= (totalDegree_mul ..).trans ((add_le_add (hY _) (hY _)).trans (by unfold D;omega))
    have hb':coin Y'≤ b^2:= (funds 0 zero_le_one ..).trans ((mul_le_mul (hf _) (hf _) (Rise.sign _ _ zero_le_one) ht).trans_eq (pow_two ..).symm)
    let a:= W (.inl j)* W (.inl u);let p:= E (.inl j)*E (.inl u)
    have hi:coin (a-p)≤ q*f+f*q:= minus_mul q q f f (hp j) (hp u) (hW (Sum.inl j)|>.1) (hE (Sum.inl u)|>.1)
    have hh: coin (shelve R h Y'-shelve (track X) h Y') ≤ g:= he' _ (b^2) (2*D) hu hb' H.races.two
    change coin (shelve _ h Y'-a - (shelve (track X) h Y'-p)) ≤ f+ g+ 2*q*f
    rw [sub_sub_sub_comm]; apply (tricolor ..).trans ((add_le_add hh hi).trans ?_); linarith only [(Rise.sign _ _ zero_le_one).trans (hp j)]

structure Awakening (p : Purse) (s : ℝ) (m : ℕ) : Prop where
  mark u (_ : u∈Set.Icc (s/2) s) :
    16*(p.era.coast.Q*walls u :ℕ)* torque u ≤ fraction m p.taylor s
  amplitude : fraction m p.taylor s ≤ knox s
  peak u (_ : u∈Set.Icc (s/2) s) :
    let B:=p.era.coast.Q*walls u
    6 * G.colorScale * (4*(B:ℝ))^2 * Paint.phase u * torque u ≤ p.sends s
  value : fault s p * Common.priced (knox s) (2*p.taylor) + defect (knox s) (p.sends s) (p.double s) (2*p.taylor) ≤ Perch.bill (-3/2) s

omit H F Z in
lemma doll (hN:k≤ N) (he : Fit C.path.levels ξ.band k x) (c) (Q B : ℕ) (k : pennant m) :
    dolmens (C:=C) (p:=p) x ξ.band Q B hN (before ..) c k=Peak.route C.path.levels ξ.band _ p Q B c:= by unfold dolmens readers; rw [he.stop]; rfl

include he

end YM.Next.Rank.Tapes
