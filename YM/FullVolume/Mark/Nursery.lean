import YM.FullVolume.Mark.Prism
/-! Rental arrows (total functions). The Gram gauge need not be separated. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{Y: Hol G}{n n': Side}{E:Desk G n}{D:Desk G n'}{a b c t v:ℝ}
open Gram
structure Club (F: Labels.Frame G d)(Y: Hol G){f n:Side}(E:Desk G f)(D:Desk G n)(a b c:ℝ) where
    flow : Gram F Y E b→ Gram F Y D a
    leanings (P:Gram F Y E b): F.Coeff ≃ₗ[ℂ] F.Coeff
    hail (P:Gram F Y E b) (i:F.Coeff):F.coeffSize i ≤b *F.coeffSize (leanings P i)
    toward P Q x: Within P Q x→ Costed (leanings P).toLinearMap (leanings Q).toLinearMap (c*x)
    trail P Q x: Within P Q x→ Within (flow P) (flow Q) (x/2)
namespace Club
variable (X:Club F Y E D a b c)(P Q : Gram F Y E b)
def drift : F.Coeff →ₗ[ℂ] Coin F Y D:= (X.flow P).g ∘ₗ (X.leanings P).toLinearMap
lemma rider (i:F.Coeff): X.drift P i = (X.flow P).g (X.leanings P i):=rfl
lemma climbs (v:F.Coeff): F.coeffSize ((X.leanings P).symm v)≤ b*F.coeffSize v:=by
    have he:= X.hail P ((X.leanings P).symm v); rw [(X.leanings P).apply_symm_apply] at he; exact he
end Club
variable {f g: Side} (h:0<a)(hf:0<b)
def tested {H:History G}{N p m:ℕ}{E:Desk G (H.S.side (m+1) p)}{D:Desk G (H.S.side m p)}{u w ξ}
        {B:SectionData F}{W:Worth}{T:Heading F}{X:Set Wing}{D':GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}(A:Tool F H N p m)(hA:Tool.Cap A B Y W D' T u ξ w X)(ha:Afford A.plate Y (H.rep N p (m+1)) (H.rep N p m))(hB:Well (H.rep N p (m+1)) E (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))(hD:Well (H.rep N p m) D (Real.sqrt (H.levels.clock.forcedAllowance m)))(hw:roomCost H.levels W)(hk:Bank W H.levels): Club F Y E D ((H.levels.params m).columns) ((H.levels.params (m+1)).columns) (ξ* (H.levels.params (m+1)).columns*Motion.orbitCost F):=
  ⟨fun Q=> Q.step A hA hB hD hw hk,fun Q=> Q.index A hA hB hw hk,fun Q x=> Q.prose A hA hB hw hk x|>.2.2,fun P Q x hx v=> (Gram.communes _ hA hB P Q ha hw hk hD hx v|>.1).trans_eq (by ring), fun Q U _ hx=> Q.revenue _ hA hB U ha hw hk hD hx⟩
-- fallback outside schedule
section sym
variable (F Y E D)
def gramZero (h:0≤a): Gram F Y E a:= ⟨0,fun i=>by simp [mul_nonneg h (Work.G08.size_nonneg F _)]⟩
def coast (h:0≤a)(hs:1≤b)(hc:0≤c): Club F Y E D a b c where
   flow :=fun _=> gramZero F Y D h
   leanings :=fun _=> LinearEquiv.refl _ _
   hail _ i:= le_mul_of_one_le_left (Work.G08.size_nonneg ..) hs
   toward _ _ x hx v:=by simpa [Frame.coeffSize] using (mul_nonneg (mul_nonneg hc hx.1) (Work.G08.size_nonneg F v))
   trail _ _ x hx:= ⟨by exact div_nonneg hx.1 zero_le_two,fun v=>by simpa [gramZero] using mul_nonneg (mul_nonneg (div_nonneg hx.1 zero_le_two) h) (Work.G08.size_nonneg F v)⟩
end sym
abbrev TwoFold (P:ℕ→Gram F Y E b) :=∀ t >0,∃ n:ℕ,∀ i≥n,∀ j≥n, Within (P i) (P j) t
abbrev NearX (P:ℕ→ F.Coeff→ₗ[ℂ] F.Coeff):Prop:=∀ t>0,∃ n:ℕ,∀ i≥n,∀ j≥n,Costed (P i) (P j) t
variable (Y':ℕ→Club F Y E D a b c)
structure Ritzy : Prop where
   paid : 0≤c
   senior : 1≤ b
   starts : 1≤ a
   plates (P:Gram F Y E b) : TwoFold (fun i=> (Y' i).flow P)
   debits (P:Gram F Y E b) : NearX (fun i=> ((Y' i).leanings P).toLinearMap)
variable {Y'}
lemma infinite {P:ℕ→ℕ→Prop}(h:∀ u v:ℕ→ℕ,Tendsto u atTop atTop→Tendsto v atTop atTop→∀ᶠ n in atTop,P (u n) (v n)): ∃ N:ℕ,∀ i≥N,∀ j≥N,P i j:=by
   by_contra! hw; choose f hf g hg H using hw
   obtain ⟨n,hn⟩:= (h f g (tendsto_atTop_mono (f:=id) hf tendsto_id) (tendsto_atTop_mono (f:=id) hg tendsto_id)).exists; exact H n hn
lemma ether (ha:1≤a)(hb:1≤b)(hc:0≤c)(hp:∀ P:Gram F Y E b, ∀ u v:ℕ→ℕ, Tendsto u atTop atTop → Tendsto v atTop atTop → ∀ x:F.Coeff, Tendsto (fun i=> (Y' (u i)).leanings P x- (Y' (v i)).leanings P x) atTop (𝓝 0)∧ Tendsto (fun i=>(Y' (u i)).drift P x-(Y' (v i)).drift P x) atTop (𝓝 0)): Ritzy Y':= by
    have he (P:Gram F Y E b)(u v:ℕ→ℕ)(hu:Tendsto u atTop atTop)(hv:Tendsto v atTop atTop):= rcost (F:=F) (V:=fun i=>(Y' (u i)).leanings P) (W:=fun i=>(Y' (v i)).leanings P) fun x=> (hp P u v hu hv x).1
    refine ⟨hc,hb,ha,fun P e hε=>infinite (fun u v hu hv=>?_),fun P e hε=>infinite (fun u v hu hv=> he P u v hu hv e hε)⟩
    let c:=e*a/((1+a)*b); have hb':= zero_lt_one.trans_le hb; have ha':= zero_lt_one.trans_le ha; have h:0<c:=by unfold c; positivity
    filter_upwards [he P u v hu hv c h, rnorm (F:=F) (V:=fun i=>(Y' (u i)).drift P) (W:=fun i=>(Y' (v i)).drift P) (fun x=>(hp P u v hu hv x).2) c h] with n ht hx; exact ridge hb' ha' ((Y' (u n)).leanings P) ((Y' (v n)).leanings P) ((Y' (u n)).drift P) _ _ _ ((Y' (u n)).hail _) (fun i=> rfl) (fun i=>rfl) ht hx h.le hε.le (le_of_eq (by unfold c; field_simp))
-- Gerbe ropes at finite heights then geometric growth
namespace Ritzy
variable {L:ℕ→Gram F Y E b} (T:Ritzy Y') (he: TwoFold L)
include T he
lemma stories : TwoFold (fun i=> (Y' i).flow (L i)):=by
     intro i hi; obtain ⟨n,hn⟩:= he (i/2) (half_pos hi)
     obtain ⟨k,hk⟩:= T.plates (L n) (i/2) (half_pos hi);
     refine ⟨max n k, fun x hx y hy=>?_⟩; obtain ⟨h,h'⟩:= max_le_iff.mp hx; obtain ⟨p,p'⟩:= max_le_iff.mp hy
     exact widen ((((Y' x).trail _ _ _ (hn x h n le_rfl)).trans (hk _ h' _ p')).trans ((Y' y).trail _ _ _ (hn n le_rfl y p))) (by linarith) (zero_le_one.trans T.starts)
lemma invests : NearX (fun i=> ((Y' i).leanings (L i)).toLinearMap):=by
     intro i hi; let c':=i/4/(c+1); have hh:= T.paid; have hc:0<c':=by unfold c'; positivity
     obtain ⟨n,hn⟩:= he c' hc; obtain ⟨k,hk⟩:= T.debits (L n) (i/2) (half_pos hi); refine ⟨max n k,fun x hx y hy=>?_⟩; obtain ⟨h,h'⟩:= max_le_iff.mp hx; obtain ⟨p,p'⟩:= max_le_iff.mp hy
     have hp: c*c' ≤ i/4:= (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hc.le).trans_eq (by unfold c';field_simp)
     refine cost_raise (cost_trans (cost_trans ((Y' x).toward _ _ _ (hn x h n le_rfl)) (hk _ h' _ p')) ((Y' y).toward _ _ _ (hn n le_rfl y p))) (by linarith)
end Ritzy
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.ether
#print axioms YM.MergeProof.Matric.Ritzy.stories
#print axioms YM.MergeProof.Matric.Ritzy.invests
#print axioms YM.MergeProof.Matric.tested
#print axioms YM.MergeProof.Matric.coast
