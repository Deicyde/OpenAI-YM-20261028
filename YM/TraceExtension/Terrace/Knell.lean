import YM.TraceExtension.Terrace.Stanza
import YM.Next.RANK.Matrices
import YM.TraceExtension.Soot.Coffer
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac Stock Labels Source
open MergeProof MergeProof.Accent Extra.Histories
open Next.Rank.Price PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
section columns
variable {G:Gauge} (C:Family G) (H:C.Makes) {d i j k N p:ℕ}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T!"=> C.factory d N p
abbrev Cturn (Y:Family G)(d k N p):= columns Y d k N p
include H
lemma nib_linear (hk:C.ref d ≤ k)(h:k≤N): IsLinearMap ℂ (Cturn C d k N p):=(( (H.calibrated d N p (hk.trans h)).linear k hk h).1.mk' _ |>.comp (T!).terminal.symm.toLinearMap).isLinear
lemma nib_unit (hk:C.ref d ≤ k)(h:k≤N) : Cturn C d k N p (C.refUnit d) = unitVec (F) C.path k:=by
    have he:= H.calibrated d N p (hk.trans h); let t:=unitVec (F) C.path N; have hx:(T!).terminal.symm (C.refUnit d) = t:=((T!).terminal.injective (by rw [LinearEquiv.apply_symm_apply,← he.reads, he.unit_coord (C.ref d) le_rfl he.ref]))
    unfold Cturn columns; dsimp; rw[hx]; exact he.unit_coord k hk h
lemma nib_faithful (hk:C.ref d ≤ k)(h:k≤N): Bijective (Cturn C d k N p):=by
    let T:= (nib_linear C H (p:=p) hk h).mk' _; have ht : Injective T:=by
        apply LinearMap.ker_eq_bot.mp
        refine LinearMap.ker_eq_bot'.mpr (fun v he=>?_)
        apply Work.G08.size_separates (F)
        have hz:= at_current C H hk h p v; change (Cturn C d k N p v)=0 at he; unfold Cturn at he; simpa only[he,Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using hz
    exact ⟨ht,LinearMap.surjective_of_injective ht⟩

omit H in
lemma drop (Y:Frame G d)(x:Y.Coeff): Y.core x=x-x 0 • Y.e0:=by
   ext1 i
   by_cases hi:i=0; · subst i; change (update x 0 0) 0= x 0- x 0*Y.e0 0; simp[Frame.e0]
   change (update x 0 0) i=x i-x 0*Y.e0 i; simp[update_of_ne hi,Frame.e0,hi]
lemma cleared (hk:C.ref d ≤ k)(hn:k<N) (v:C.label d):
    (F).coeffSize ((F).core (Cturn C d k N p v)) ≤ (C.path.levels.params (k+1)).columns * ((C.S.block k).val:ℝ)^d * (F).coeffSize ((F).core (Cturn C d (k+1) N p v)):=by
    let i:=k+1; let X:= Cturn C d k N p v; let Y:= Cturn C d i N p v; let L:= ((C.S.a (k+1):ℂ)^d); let w:= Y 0/L; let f:=v-w • C.refUnit d; let hK := (nib_linear C H (p:=p) hk hn.le).mk' _; let hz:= (nib_linear C H (p:=p) (hk.trans k.le_succ) hn).mk' _
    have hp :(F).core X=(F).core (hK f):=by
        have hv:(F).core (F).e0=0:= by rw[drop];simp[Labels.Frame.e0]
        unfold f; rw[map_sub,map_smul,show hK (C.refUnit d)=_ from nib_unit C H (p:=p) hk hn.le,map_sub]; simp only[map_smul,unitVec,hv,smul_zero,sub_zero];rfl
    have hR : hz f=(F).core Y:=by
       unfold f; rw[drop,map_sub,map_smul,show hz (C.refUnit d)=_ from nib_unit C H (p:=p) (hk.trans k.le_succ) hn]; congr 1; change w • (L • Frame.e0 _) = _; rw[smul_smul]; unfold w; rw [div_mul_cancel₀]; exact pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
    change (F).coeffSize ((F).core X)≤_*_* (F).coeffSize ((F).core Y); rw[hp,← hR]; exact le_trans (Work.G08.size_core ..) ((H.calibrated _ _ p (hk.trans hn.le)).front k hk hn ((T!).terminal.symm f))
-- star and signed orientation receipts from the Songs
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {ζ:ℕ→ℕ→ℝ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (hr:Scrim C W u ψ φ δ ζ r D)
include hr
lemma guarded (hk:C.ref d ≤ k)(h:k≤N)(v:C.label d)(s:Signed):
    Cturn C d k N p (star v)=star (Cturn C d k N p v) ∧ Cturn C d k N p ((F).act s.ortho v)=(F).act s.ortho (Cturn C d k N p v):=by
    let V:= C.factory d N p; obtain ⟨M,hM,hL,hC,hH⟩:= (hr.costs.aim d N p (hk.trans h)).lyrics
    let w:= V.terminal.symm v; have hp:= H.calibrated _ _ p (hk.trans h)
    have hs:= (Sung.clocks _ _ _ _ _ W (C.ref d) M hL).moves k hk h w
    have hb' : (T!).terminal.symm (star v)=star w:= V.terminal.injective (by rw[LinearEquiv.apply_symm_apply,hp.realForm,show (T!).terminal w=v from V.terminal.apply_symm_apply v]); have ht : (T!).terminal.symm ((F).act s.ortho v)=(F).act s.ortho w:= V.terminal.injective (by rw [LinearEquiv.apply_symm_apply,hp.orients,show (T!).terminal w=v from V.terminal.apply_symm_apply v]);
    change (((T!).entries k _).x=_)∧(((T!).entries k _).x=_); rw [hb',ht,hM]; simp only[Cturn,columns,hM]; exact ⟨hs.1,hs.2 s⟩
omit H hr
end columns
section ladder
variable {G:Gauge}
def gear (A:Levels G)(j:ℕ):ℝ:=2*(1+(A.params (j+1)).columns)/ PhysicalNext.Repeat.Quince.cameo A (j+1)
lemma gear_pos (A:Levels G) (i:ℕ): 0< gear A i := div_pos (by have hp:= (A.params (i+1)).columns_ge; positivity) (cameo_pos ..)
-- uniform for ANY K:N periods suitably large
structure Sceptre (C:Family G) (W:Bid.Worth) : Prop where
    step : ∀ d m,d≤5 → C.ref d ≤ m→∀ᶠ p:ℕ in atTop,∀ N:ℕ,m < N → ∀ v:C.label d,
        let P:=C.path.levels; let a:=(P.budget m).threshold; let b:=(P.budget (m+1)).threshold; let w:= Cturn C d (m+1) N p v;let X:= C.labels.level d
        b/a≤2 ∧ X.coeffSize ((Cturn C d m N p v)- X.scaled (a/b) (Bid.vowel X (C.S.block m) w)) ≤ gear C.path.levels m * X.coeffSize (X.core w)
    bias : ∀ d k,C.ref d≤ k →∀ᶠ p:ℕ in atTop,∀ N:ℕ,k≤N → SharpRead C N k p d (W:=W) (cameo C.path.levels k)
end ladder
end YM.Trace.Terrace
