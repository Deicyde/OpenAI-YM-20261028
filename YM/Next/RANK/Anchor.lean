import YM.Next.RANK.HomeSync
import YM.Next.RANK.License
import YM.Next.RANK.Pension


/-!
# k output with multi-array input exactly stated

No weakening terminal weight obligations. Use this only on wallets with all input
prices of earlier nodes delivered. Stake is a missing multi-mark value-order
local estimate, on the OLD threshold at level k, before the restoration or
any finite-normalized comparison. Intended for proof via RBin/RMix precursors,
not claiming standard RMixed caps are for these mark radii, locations etc. Reorganization to terminal retention consumes
additional local-step estimates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 512
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {C : Family G} {ι κ χ μ V : Type}
variable {N k d p m i : ℕ} {q : BudgetPoint}

-- Stake's existential can include padding finite types using F.C paths.
section
variable (m : ℕ) (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : Fin (m+1)→C.label d)
variable {B : Neat (C.side k p)→Burst G (C.side k p) (C.path.rep N p k).p.threshold}
variable (h : C.Makes) (hp : C.ref d≤k) (F : Course C N p k) (y : ℝ)

-- M-mix input at this probe only. Y includes all orientation hands. may generalize producer.
def Stake := let Q:= C.path.rep N p k; let f:= seats C b Y hN p
    ∃ (B : Neat (C.side k p)→ Burst G (C.side k p) Q.p.threshold), IsoVac _ B (C.path.levels.clock.forcedAllowance k) ∧
      ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ),∃ (A : ι→SourceAt G f) (K : κ→Lifted G f Q.p.threshold),
        Unpacks A Q.p (fun _=> y) Q.p.supportExponent 1 ∧ Unfold (p:=Q.p) K (fun _=> y) Q.p.supportExponent 1 ∧
        (∀ i, 2≤(A i).fires.val.card) ∧ (∀ i,2≤ (K i).fires.val.card) ∧
        ∀ U T, 2 ≤ (T.val: Finset (Listens C b (v:=m+1) hN p)).card →
          (fabricated Y hN b v B A K h hp U).part T=(Bills C b Y hN p v F U).part T
end

variable (m i : ℕ) (Y : Points (m+1)) (b : ℝ) (hN : k≤N) (v : Fin (m+1)→C.label d)
variable {Q : Rep G (C.side k p)} {X : Keepat (C.side k p)} {w : Fin (m+1) → Config G (C.side k p)→ℂ} {c : Fin (m+1)→ℝ}
variable (h : C.Makes) (hp : C.ref d≤k) (ht : ∀ j,Ticket (v j) i k N p Q.p X (w j) (c j)) (F : Course C N p k)

-- blank checks must hold from calibrated stage construction

def debit (q : BudgetPoint) (P : Support n) (e a : ℝ) := 3*a*debt q.B e (halo 8 P)

def drain (i : ℕ) (p : BudgetPoint) (_ : BudgetPoint) (a e γ : ℝ) := Real.exp (-γ)+Real.exp (100000*(e+2))*Real.exp (-(p.supportExponent * i)/2)*a

def strand (P : Support n) (i : ℕ) (p q : BudgetPoint) (a e γ : ℝ) :=
    wilt q.B * debit q P (e+2) a + wilt q.B * drain i p q a e γ

def mech (w : ℝ) (q : BudgetPoint) (a e γ : ℝ) := plane w e + wilt q.B * (Real.exp (100000*(e+2))*(a*Real.sqrt w)) + wilt q.B * (Real.exp (-γ)*1)

def Rod (Q : Rep G (C.side k p)) (W : Listens C b (v:=m+1) hN p→ SourceAt G (seats C b Y hN p)) (e r w K : ℝ) := ∃ (ι κ : Type), ∃ (_ : Fintype ι) (_ : Fintype κ),
    ∃ (H : ι→ SourceAt G (seats C b Y hN p)) (Y' : κ→Lifted G (seats C b Y hN p) Q.p.threshold),
      Bills C b Y hN p v F=dust Q (Sum.elim H W) Y' ∧ Background Q Y' ∧ Unpacks H Q.p (fun _=>r) e w ∧ Alarm.prepared (q:=Q.p) Y' (fun _=>r) e K

lemma delivered (hV : Spaced (C.path.rep N p k).p.B (seats C b Y hN p))
    (X' : Siren G (C.side k p) Q.p.threshold) (W : ValidX _ → Wickless G _ Q.p.threshold) {r a e z β σ Λ d' c' δ w' γ : ℝ}
    (ℓ : Lower (C.path.rep N p k).p Q.p) (hu : 0<a) (hz : 0≤z) (he : 0≤e) (hr : 0<r) (hy : 0≤ w') (hs : 0≤d')
    (H : BudgetMix (C.path.rep N p k).p Q.p r a (e+2) γ) (hW : ∀ j, 0≤c j) (hH : scalesExp (C.path.rep N p k).p Q.p (2*(e+2)))
    (J : Stake m Y b hN v h hp F r)
    (hB : Bridges (C.path.rep N p k) Q e z σ β Λ δ X' W (q:=Q.p))
    (hT : ∀ j,a*moneys C d k N p (v j) ≤ w') (hx : ∀ j,a*c j ≤ c')
    (hQ : 2*vacancies e Λ σ β δ (C.path.β N p k) (C.path.rep N p k).p Q.p + strand X.val i (C.path.rep N p k).p Q.p w' e γ +
      mech (C.path.levels.clock.forcedAllowance k) Q.p w' e γ +batch z (e+1) Q.p.B ≤ d')
    (hA : (↑((Q.p.B+Q.p.B+1)^4:ℕ):ℝ)*d' ≤ 1) :
      Rod m Y b hN v F Q (readyH m i Y b hN v ht) e a (c'*debt Q.p.B e X.val + drain i (C.path.rep N p k).p Q.p w' e γ) (Real.exp (-z)*(Real.exp d'-1)):= by
  let P:= C.path.rep N p k; let t:=fun _ : Listens C b (v:=m+1) hN p=> a; let QW:=wilt Q.p.B
  let Cw:=readyH m i Y b hN v ht
  obtain ⟨B,h1,ι,κ,hi,hk,A,L,hL,hM,hP,hR,hV'⟩:=J
  let Xw := readyWide m i Y b hN v h hp (p:=p)
  let G':= Sum.elim A Xw; let Y':=Sum.elim (ensembleO Y hN b v B h hp) L
  let U := drain i P.p Q.p w' e γ; have H' : 0 ≤ U:= by unfold U drain; positivity
  have hE : (e+1)+1=e+2:=by ring
  have hc:Credit G' P.p Q.p t (e+2) U:= by
    have ht := Credit.mix (transfer _ hL hP H hr hu hV) (clouds m i Y b hN v t h hp (fun _=> hu.le) (show 0 ≤e+2 by linarith) ℓ hH (fun i=>hT _))
    apply Credit.relax ht; unfold U drain P; simp
  have hX : scalesExp P.p Q.p (e+1+1) := by apply le_trans _ hH; gcongr; linarith only [he]
  let P1:=stand m i Y b hN v A h hp ht ℓ.good
  let s2:=strand X.val i P.p Q.p w' e γ
  let s3:=mech (C.path.levels.clock.forcedAllowance k) Q.p w' e γ
  have hip:= injected P.p.B _ P.p.B_pos hV
  have hv' : taxable (q:=Q.p) P1 t (e+1) s2 := by
    have hh:=dash_credit P.p Q.p (show Credit G' P.p Q.p t (e+1+1) U from hE.symm ▸ hc) ℓ.good hip H'
    have hz:= ember_cost m i Y b hN v t h hp ht (fun j=> hu.le) (add_nonneg he zero_le_one) (fun j=> hT j.2) hip (ℓ:=ℓ.good)
    apply Edition.taxable.relax (Edition.taxable.add hz hh); rw [hE]; exact le_rfl
  have hY : Burden Y' Q.p t (e+1) s3:= by
    have hs:= farer Y hN b v h hp B h1 t (fun _=> hu.le) ℓ (add_nonneg he zero_le_one) hV hX (fun i=>hT i.2)
    have hk:= rooted_interest hM hR (show BudgetMix P.p Q.p r a (e+1+1) γ from hE.symm ▸ H) hr hu (add_nonneg he zero_le_one) zero_le_one hV
    apply Edition.Burden.up Q.p (sum_token _ _ _ hs hk); rw [hE]; exact le_rfl
  let K:=teat Y' (Sum.elim (fun i=> (W i).credit (seats C b Y hN p)) P1) X'
  refine ⟨_,_,inferInstance,inferInstance, rested m i Y b hN v A h hp ht,K,?_,?_,?_,?_⟩
  · rw [prepaid Y hN b v B A L F h hp h1 hV' hP hR];
    exact funext fun U=> assembled m i Y b hN v A L h hp ht X' W ℓ.good hB U
  · let V':=Sum.elim (fun i=> (W i).credit (seats C b Y hN p)) (stand m i Y b hN v A h hp ht ℓ.good)
    let E:Y' = Sum.elim (ensembleO Y hN b v B h hp) L:=rfl
    have he : Nonempty (Germs B W Y' V') := by
      refine ⟨⟨⟨fun i=> .inl (.inl i),fun x y h=> Sum.inl.inj (Sum.inl.inj h)⟩,⟨.inl,fun _ _ h=>Sum.inl.inj h⟩,fun _=>rfl,fun _=>rfl,?_,?_⟩⟩
      · rintro ((x|x)|x) H
        · exact ⟨x,rfl⟩
        · have hQ:slot x.1=quiet _:=H
          obtain ⟨a,ha⟩:= (singleton_nonempty x.1); exact False.elim (notMem_empty a (show a∈(quiet _).val from hQ ▸ (show a∈(slot x.1).val from ha)))
        have ht:= hR x; change (L x).fires= _ at H; rw [H] at ht; change 2 ≤ (∅: Finset _).card at ht; rw [card_empty] at ht; omega
      rintro (x|x) H
      · exact ⟨x,rfl⟩
      have ht':= standMode m i Y b hN v A h hp ht ℓ.good x
      change (stand m i Y b hN v A h hp ht ℓ.good x).fires=_ at H; rw [H] at ht'; exact False.elim (not_nonempty_empty ht')
    obtain ⟨E⟩:=he; exact fun j U=> (Germs.background X' E j U).trans (hB.jacket B h1.points h1.value j U)
  · apply Unpacks.mix (roil m i Y b hN v t h hp ht (fun i=> hu.le) hW (fun i=> hx i.2))
    exact Credit.spill t hc ℓ.good (by linarith only) he
  exact Alarm.rarity Y' _ X' (fun i=> hu) (Edition.taxable.add (Alarm.salary _ hB.remain t) hv') hY hB.head hA hQ he hz hs
end YM.Next.Rank.Edition
