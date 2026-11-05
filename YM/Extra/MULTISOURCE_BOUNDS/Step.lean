import YM.Extra.MULTISOURCE_BOUNDS.Scheme
import YM.Work.A05.Window
import YM.Work.B09.Shell

/-!
# An optional quantitative proof of Raw on a component/overlap trajectory

Prices derived by `System.price`, subject to actual vertex hypotheses of
Scheme + Forward and suitable Scope inflation. Kernel identities, choices
of integrated alphabets, valuation/suppression and the first-system
per-component integration estimate are NOT established from the gauge
setup. See Scheme comments. No recalibration across offers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.System
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Germs Merger Repeated
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff

variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {N p m : ℕ}
  {D : V→ℕ} {s : Scope} {loss : Tariff} {d : ℕ→ℕ} {ζ : ℕ→ℝ}
  {A : Bands R (C.path.rep N p m)} {A' : Bands R (C.path.rep N p (m+1))}

omit [Fintype V] [DecidableEq V] in
private lemma unmarkedPool {Z : Layer G V (C.side m p)} {w : V → ℝ} {e : Z.Id → ℝ} {M : ℕ} {a b γ}
    (h : Ac.Hit Z.supp M e a b) (he : ∀ i,0 ≤ e i) (hy : b ≤ γ) (hh : 0 ≤ γ) (ht : ∀ i,Z.names i=∅) :
    Pool Z.names Z.supp M a (Z.weighted w e) γ γ := by
  rw [show Z.weighted w e = e by ext i; simp [Layer.weighted,duty,ht]]
  exact ((Pool.vac h he hh ht).mono he (fun _ => le_rfl) le_rfl le_rfl hy)

private lemma sourcePool {β : Type} {names : β → Finset V} {X : β → Support (C.side m p)}
    {e : Pieces → ℝ} {g : β → ℝ} {w : V → ℝ}
    (H : Prepared s (extra loss) C.localSection C.path.levels)
    (hc : Certified s loss d ζ C.params C.labels C.path.levels)
    (hξ : 7 ≤ s.inflate (year C (m+1))) (hμ : Occupancy A.origins (s.markers (year C m)))
    (hw : ∀ v,0 ≤ w v) (he : ∀ i,0 ≤ e i) (hg : ∀ i,0 ≤ g i)
    (hroot : Rooted (bids A') (blocks A') (point C (m+1)).B (point C (m+1)).supportExponent
      (fun i => duty w (bids A' i)*e i) 1)
    (hfork : Fork (bids A') (blocks A') names X A.origins (C.path.levels.clock.op m p).ratio (s.expand (year C (m+1)))
      (point C m).B (point C (m+1)).B (d (year C (m+1))) e g (quote C m loss)) :
    Pool names X (point C m).B ((point C m).supportExponent+6) (fun i => duty (fun v => w v / quote C m (extra loss))
      (names i)*g i) (tollCap s C m/2) (tollCap s C m/2) := by
  let P := point C m; let Q := point C (m+1)
  let t := extra loss; let j := year C (m+1); let r := s.expand j
  let a := P.supportExponent+6
  have ha : 0≤a+1 := by dsimp only [a]; linarith [P.exponent_pos]
  let fee := quote C m loss
  let b := quote C m t
  let S := pad (a+1) Q.supportExponent r (d j) * fee / b
  let μ := s.markers (year C m)
  let Δ := tollCap s C m/2
  have hfee : 1 ≤ fee := quote_ge ..
  have hb : 1 ≤ b := quote_ge ..
  have hT : 1 ≤ pad (a+1) Q.supportExponent r (d j) := pad_ge ha
  have hS : 0 ≤ S := by unfold S; positivity
  have hA : 20*(a+1)*tilePrice r ≤ (C.S.block m).val*Q.supportExponent := by
    refine le_trans ?_ (s.shape (H.shapes m)); change 20*_*_ ≤ 20*(Q.supportExponent + _)*_
    have ht : P.supportExponent ≤ Q.supportExponent := C.path.levels.fits.deepExp (Nat.le_succ _)
    gcongr 20*?_*_; change a+1 ≤ Q.supportExponent + s.inflate j; unfold a j; linarith
  have hM : Q.B ≤ 2*P.B := by
    have ht : Q.B^2 ≤ 2*P.B^2 := H.tabs.grows _; by_contra! hh; nlinarith only [hh,ht]
  have hr := hfork.rethread (τ:=b) (zero_le_one.trans hfee) hg P.B_pos hM ha Q.exponent_pos hA hw hb he hroot
  rw [mul_one] at hr
  have Hc : (1+μ*siteFactor P.B)*S ≤ Δ := by
    unfold S; rw [← mul_div_assoc,← mul_assoc,show a+1=P.supportExponent+7 by unfold a; ring]; change ticket (C.path.levels.params m) (C.path.levels.params (m+1)) r _ _ (d j) * _ / _ ≤ _
    exact (hc.cost m).1
  have hc' : 0 ≤ (μ:ℝ)*siteFactor P.B := by unfold siteFactor; positivity
  let z i := duty (fun v => w v/b) (names i)*g i
  have hz i : 0 ≤ z i := mul_nonneg (prod_nonneg fun v _ => div_nonneg (hw _) (zero_le_one.trans hb)) (hg i)
  have he' := root_hit hμ hz hS (fun i (hi : 0<z i) => ?_) hr
  refine ⟨hz,fun x => Budget.mono (he' x) ((he' x).1) (fun _ => le_rfl) (by change μ*siteFactor P.B*S ≤ Δ; linarith), hr.mono hz (fun _ => le_rfl) (by change a ≤ a+1; linarith) (by change S ≤ Δ; nlinarith)⟩
  obtain ⟨_,h,_⟩ := hfork.bill
  obtain ⟨_,v,hv,hv',_⟩ := h i (by contrapose! hi; unfold z; rw [le_antisymm hi (hg i),mul_zero])
  exact ⟨v,hv,hv'⟩

/-- Conditional one-step consumer advancing RMixed. `hξ` concerns exactly
the pre-L choices: reserve the seven extra projected exponents (budget proof
in `Scope.shape`, shrinking under this projection, no within-plateau loan of
an exponent at every level). Still requires every *primitive* field and
vertex estimate of Forward, not just an exact formal propagation.
-/
theorem Forward.step {F : Scheme C D A} (h : Forward F A' s loss d ζ) (hC : C.Makes)
    (hm : m < N) (HA : A.Active) (hD : ∀ v,C.ref (D v) ≤ m)
    (H : Prepared s (extra loss) C.localSection C.path.levels)
    (hc : Certified s loss d ζ C.params C.labels C.path.levels)
    (hξ : 7 ≤ s.inflate (year C (m+1))) (hμ : Occupancy A.origins (s.markers (year C m))) :
    Raw C A A' D (extra loss) := by
  intro w hw he
  obtain ⟨e,he,hroot⟩ := inbox A' (divisor_pos C (m+1)) (fun v => (hw v).le) he
  rw [(hC.wilson.represents N p (m+1) hm).vac] at hroot
  obtain ⟨a,b,t,g,k,ha,hb,ht,hk,hfork,hvac,hreset,hg,hR,hK⟩ := h.costs e he
  let P := point C m
  let ξ := P.supportExponent
  let u v := w v / quote C m (extra loss)
  let ε := tollCap s C m
  have hu v : 0 ≤ u v := div_nonneg (hw _).le (zero_le_one.trans (quote_ge ..))
  have hε : 0 < ε := inv_pos.mpr bank_pos
  have hξ' : 0 < ξ := P.exponent_pos
  have hz i : 0 ≤ duty w (bids A' i)*e i := mul_nonneg (prod_nonneg fun v _ => (hw v).le) (he.pos i)
  have hA := sourcePool H hc hξ hμ (fun v => (hw v).le) he.pos ha (hroot.mono hz (fun _ => le_rfl) le_rfl (pow_le_one₀
      (gHat_pos ..).le (gHat_le_one ..))) hfork
  have hB := unmarkedPool (w:=u) hvac hb (hc.cost m).2 (by positivity : 0 ≤ ε/2) F.no_marks
  let X := F.marks.combine F.vac
  let weight := Sum.elim a b
  have hX : Pool X.names X.supp P.B (ξ+6) (X.weighted u weight) ε ε := by
    rw [show ε=ε/2+ε/2 by ring]; unfold X weight; rw [Layer.combine_weighted]; exact hA.join hB
  let j := Layer.logPrice P
  let R := overheadAt C.params C.labels (C.path.levels.params m) (year C m) (s.markers (year C m)) P.B
  let M := ((P.B+P.B+1:ℕ):ℝ)^4
  let pmax := j*R*ε
  have hj : 1≤j := logBudget_one (S:=(C.path.levels.params m))
  have hR' : 1≤R := overheadAt_one
  have hM : 1≤M := one_le_pow₀ (by exact_mod_cast (show 1 ≤ P.B + P.B + 1 by omega))
  have hP : 0≤pmax := by unfold pmax; positivity
  have hJ : 0 ≤ j := zero_le_one.trans hj
  have hζ : j*ε ≤ pmax := by unfold pmax; gcongr; exact le_mul_of_one_le_right hJ hR'
  have hε' : ε ≤ pmax := (le_mul_of_one_le_left hε.le hj).trans hζ
  have heq : ε = (256*M*j*R)⁻¹ := rfl
  have small : 256*M*pmax ≤ 1 := by dsimp only [pmax]; rw [heq]; apply le_of_eq; field_simp
  have hpass (x : ℝ) (h : x ≤ 32*pmax) : 8*((P.B+P.B+1:ℕ):ℝ)^4*x ≤ 1 := by change 8*M*x ≤ _; nlinarith only [small, mul_le_mul_of_nonneg_left h (zero_le_one.trans hM)]
  have hfinish : 64*pmax ≤ 1 := by nlinarith
  have issue {ι : Type} (names : ι→Finset V) (Y : ι→Support (C.side m p)) (c : ι → ℝ) (hc : ∀ i,0≤c i)
      (hh : Display X.names X.supp names Y weight c 1) :
      Pool names Y P.B (ξ+5) (fun i => duty u (names i)*c i) (2*ε) (2*ε) := by
    have h := (show Pool X.names X.supp P.B ((ξ+5)+1) (X.weighted u weight) ε ε from (by rw [show ξ+5+1=ξ+6 by ring]; exact hX)).resold
      hh hu hc (by linarith : 0≤ξ+5) hε.le (hpass _ (by linarith)) hε.le zero_le_one
    rwa [one_mul] at h
  have I₁ := issue _ _ g (fun i => (hg i).2.2.1) hR
  have I₂ := issue _ _ k (fun i => (hk i).1) hK
  obtain ⟨f,hf,hG,hN⟩ := F.reg.logs P u (a:=ξ+3) (b:=2*ε) g hu (by linarith) (by positivity) (hpass (2*ε) (by linarith)) (by positivity) hg
    (by rw [show ξ+3+2 = ξ+5 by ring]; exact I₁)
  let exp := F.reg.log
  have hG : Pool exp.names exp.supp P.B (ξ+3) (exp.weighted u f) (4*j*ε) (4*j*ε) := by
    rw [show 4*j*ε=j*(2*(2*ε)) by ring]; exact hG
  obtain ⟨f',hf',hP'⟩ := F.cut.invoice hC hD hμ (fun v => ((H.here m).atlas (D v) (admitted _ _ hC (hD v))).1) f u hu (by positivity) hf hG.root
  have hP' := hP'.mono hP'.positive (fun _ => le_rfl) le_rfl (show R*(4*j*ε) ≤ 4*pmax by unfold pmax; linarith) (show R*(4*j*ε) ≤ 4*pmax by unfold pmax; linarith)
  let Y := (F.reg.negative P).combine F.reset
  let v := Sum.elim f t
  have hRenew := unmarkedPool (w:=u) hreset (fun i => (ht i).1) ((hc.cost m).2.trans (by linarith : ε/2 ≤ ε)) hε.le F.no_renew
  have hY : Pool Y.names Y.supp P.B (ξ+2+1) (Y.weighted u v) (5*pmax) (5*pmax) := by
    have he : Pool Y.names Y.supp P.B (ξ+3) (Y.weighted u v) _ _ := (Layer.combine_weighted ..) ▸ hG.join hRenew
    exact he.mono he.positive (fun _ => le_rfl) (by linarith) (by linarith) (by linarith)
  obtain ⟨L,hL,hpool⟩ := F.restore.estimate _ _ _ u hu (b:=2*pmax) (b':=5*pmax) (γ:=2*pmax) (γ':=5*pmax) (by linarith : 0 ≤ ξ+2)
    (show 0 ≤ 2*pmax+5*pmax by positivity) (by positivity) (hpass _ (by linarith)) (divisor_pos C m).le (divisor_le ..) hk
    (show Y.Covers v 1 from Sum.rec hN ht) (I₂.mono I₂.positive (fun _ => le_rfl) (by linarith) (by gcongr) (by gcongr)) hY
  obtain ⟨k',hk',hfinal⟩ := F.finish.estimate _ _ _ u hu (b:=2*(2*pmax+5*pmax)) (γ:=2*(2*pmax+5*pmax)) (b':=4*pmax) (γ':=4*pmax) (by linarith : 0 ≤ ξ+1) (by positivity) (by positivity) (hpass _ (by linarith))
    (divisor_pos C m).le (divisor_le ..) hL hf' (by rw [show ξ+1+1=ξ+2 by ring]; exact hpool) (by rw [show ξ+1+1=ξ+2 by ring]; exact hP')
  have hq : 1 ≤ quote C m (extra loss) := quote_ge ..
  refine F.raw_cost hC hm.le HA w (fun v => (hw v).le) f k' (fun i => ⟨(hf i).1,(hf i).2.2⟩) hk'
    (hG.root.mono hG.positive (fun _ => le_rfl) (by change ξ+1 ≤ ξ+3; linarith) (by linarith only [hζ,hfinish,hq,hP]))
    (hfinal.root.mono hfinal.positive (fun _ => le_rfl) le_rfl (by linarith only [hfinish,hP,hq]))

end YM.Extra.Multi.System
