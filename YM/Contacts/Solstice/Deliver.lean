import YM.Contacts.Solstice.Gates
/-!
# Using the radius-dependent inspector on the actual estimates

Length `s` entering, cost of projection using high comparison index, small-geometry end.
Since the inspector is a smooth interpolation in coordinates at each weight, can *exactly*
replace it by a fixed probe when reading its represented weight past its admission threshold.
This also proves there is no ambiguity in that step between reading the whole smooth prescription
at a smaller scale than the currently registered stage patch and reading the stipulated fixed
projection for a particular term; as long as the necessary apertures and horizons are respected,
the row equals. No need to modify the reader used on the subsequently reached internal scales.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{Z:Final C F S}
variable {M : Devices Z.sector.derivatives} {E I W V J : Type}
 [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ} {P:E→ₗᵢ[ℝ] Points k}{g : Normal.Group k}
local notation "GN"=> Normal.Group k
local notation "E!"=> Expression Z.sector.derivatives
-- changing exterior/parameter

def pullBank {Q : Pieces g} (r:Route P Q I W) (f : V→W) : Route P Q I V where
   ceiling:= r.ceiling
   allows:= r.allows
   length:= r.length ∘ f
   offset:= r.offset ∘ f
   diameter i:= r.diameter i ∘ f
   frame:= r.frame ∘ f
   stage:= r.stage ∘ f
   register := r.register
   tagalong:= r.tagalong
   leading:= r.leading
   reserve:= r.reserve
   positive:= r.positive
   short v:= r.short (f v)
   accounted i v:= r.accounted i (f v)
   aligned v i:= r.aligned (f v) i
   displaysNormals:= r.displaysNormals
   accommodates v i:= r.accommodates (f v) i
   in_budget v i:= r.in_budget (f v) i
   limited_stage v := r.limited_stage (f v)
   closedStage v:= r.closedStage (f v)
   clear v i:= r.clear (f v) i

namespace Thresholds
variable (T:Thresholds M)(r:Route P (root g) I W)
variable (hg : g.Nonempty)
-- graded version through each n, call activeRow, and extracted cap values sit in W_{≤enter}. no assertion of convergence as that cap varies; we pay aperture for it to read at all.

def records (n:ℕ) (s:ℝ) (x:E4):= (T.activeRow n s x)
def reaches (n:ℕ)(s:ℝ)(x:E4):= (M.project x n).comp (T.display s x)
lemma cap_reaches (s:ℝ)(_hs:0<s)(x:E4)(e:Expression Z.sector.derivatives) : insertField M.basis x (T.enter s) (T.reaches (T.enter s) s x e)= T.display s x e:= by
    change M.replaceAt x (T.enter s) (T.display s x e)=_; unfold display projectSum; rw [LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun i hi=>?_; rw [LinearMap.smul_apply,map_smul,Devices.insertRow,LinearMap.comp_apply,M.replace_id _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
lemma reaches_row {n v : ℕ}(s:ℝ)(hs:0<s)(x:E4)(f: Expression Z.sector.derivatives)(hv:v≤ n):
    M.splitting.part v n (T.reaches n s x f) = T.activeRow v s x f:= by unfold reaches; rw [LinearMap.comp_apply,M.select_grade _ hv,T.active_row v s hs]
lemma return_grade {n : ℕ}(u:ℝ)(hp:0<u)(hh:u≤ T.time n)(x:E4)(p:E!) : T.reaches n u x p = M.project x n p:= by
    have h := T.expand_to hp hh x p -- M.replaceAt x n not project identity
    -- apply `M.project` so have equality
    exact (M.project_id x n (T.reaches n u x p)).symm.trans ((congr_arg (M.project x n) h).trans (M.project_id x n _))
lemma return_row {n : ℕ}(u:ℝ)(hp:0<u)(hh:u≤ T.time n)(x:E4) : T.activeRow n u x= M.row x n:= by rw [activeRow, T.turns n hp.le hh, Complex.ofReal_one,one_smul]
-- reader with fixed truncation of smoothly indexed expression, at declared scale explicit.
def rightNow (Y : W→ ℝ)(n:ℕ) : Reader E W (S.Field n) k Z.sector.derivatives := fun w x=> (T.activeRow n (Y w) (r.oculus w g x)).comp eraseTags.toLinearMap
def rightThrough (Y : W→ℝ)(n:ℕ) : Reader E W (S.Field n) k Z.sector.derivatives := fun w x=> (T.reaches n (Y w) (r.oculus w g x)).comp eraseTags.toLinearMap
lemma enough_row {Y:W→ℝ}{n:ℕ}(he:∀ w,Y w∈Ioc 0 (T.time n)): T.rightNow r Y n= rootCoeff r M n := by funext w x; unfold rightNow rootCoeff; rw [T.return_row (Y w) (he w|>.1) (he w|>.2)]
lemma enough_full {Y:W→ℝ}{n:ℕ}(he:∀ w,Y w∈Ioc 0 (T.time n)): T.rightThrough r Y n= rootProjection r M n := by funext w x; unfold rightThrough rootProjection; congr 1; exact LinearMap.ext (T.return_grade (Y w) (he w|>.1) (he w|>.2) _)
-- compatibility and apertures at any used n. No need angular cover dependent changes.
def catches (w : W)(s : ℝ) (A : ℝ) : Prop := s>0 ∧ A ≥ r.reserve * r.R g w ∧ A ≤ M.clearance (T.enter s)
include hg in
lemma rhymes {w : W}{u A:ℝ}(h:T.catches r w u A) (n:ℕ) (hn : n ≤ T.enter u) : r.stage w ⊆ strip (normalOn P g) (M.clearance n) := by
   intro y hy; have hh:= (show ‖(normalOn P g).starProjection y‖ ≤ r.R g w*r.reserve from r.proportions (clasp g hg) w hy);
   exact hh.trans ((mul_comm ..).le.trans (h.2.1.trans (h.2.2.trans (M.antitone_clearance hn))))
lemma period (C:ℝ) : ∀ᶠ s:ℝ in 𝓝[>] 0,∀ w, r.R g w ≤ C*s → T.catches r w s (r.reserve*C*s):= by
   filter_upwards [T.ripe (r.reserve*C), self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with x hx hxr w hw using ⟨hxr,by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw (zero_le_one.trans r.positive),hx⟩

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [Fintype I]
variable {d : Fin k→ℕ} (X : W→ Cells S d)
variable (w:W)(f : Menu k)(p:SmoothTests E)
omit [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] [Fintype I] in
lemma at_row {i n : ℕ} (h:i≤n)(Y : W→ℝ)(hh:0< Y w) (x:E) :
   r.windings M (T.rightNow r Y i) X f w p x = M.splitting.part i n (r.windings M (T.rightThrough r Y n) X f w p x):= (T.reaches_row (Y w) hh _ _ h).symm -- when not unit r
omit [MeasureSpace E] [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] [Fintype I] in
lemma small_turn {i : ℕ}(Y: W→ℝ)(u : ℝ)(hv:Y w=u) (x:E) : r.windings M (T.rightNow r Y i) X f w p x= (↑(T.gate i u):ℂ) • r.windings M (rootCoeff r M i) X f w p x:= by subst u; rfl

variable (s : W→ℝ)(H : Services C F S)(hm : r.Authority M d)(hp : tsupport p.val ⊆ r.stage w)(hT : Given X)
include H hm hp hT hg
lemma each_weight (n : ℕ) (hw : r.stage w ⊆ strip (normalOn P g) (M.clearance n)) : Integrable (r.windings M (rootCoeff r M n) X f w p):= by
    let x(_:Unit):=w; let q:=pullBank r x; let D:=coefficient_loan q hg M n (fun _=> hw) H
    have he : q.windings M (rootCoeff q M n) (X ∘ x) f () p=r.windings M (rootCoeff r M n) X f w p:= rfl; rw [← he]; exact readable (r:=q) (T:= X∘x) f () p D (given_drops X x hT) (show q.Authority M d from hm) H hp
lemma full_circle (n:ℕ) {A:ℝ}(h:T.catches r w (s w) A)(hn : n≤ T.enter (s w)):
       Integrable (r.windings M (T.rightThrough r s n) X f w p) ∧
       ∀ j≤n,M.splitting.part j n (∫ x,r.windings M (T.rightThrough r s n) X f w p x)=∫ x,r.windings M (T.rightNow r s j) X f w p x:= by
   let F:= r.windings M (T.rightThrough r s n) X f w p; let u(i:ℕ):= r.windings M (T.rightNow r s i) X f w p; have he (i:ℕ)(hi:i≤n) : Integrable (u i):= by
      unfold u; rw [funext (small_turn T r X w f p s (s w) rfl (i:=i))]; exact (each_weight r hg X w f p H hm hp hT i (T.rhymes r hg h i (hi.trans hn))).smul (↑(T.gate i (s w)):ℂ)
   let L(i:Fin (n+1)):=LinearMap.toContinuousLinearMap (Z.sector.derivatives.rise (Nat.le_of_lt_succ i.isLt)); have hL(i:Fin (n+1)): (i:ℕ) ≤ n:=Nat.le_of_lt_succ i.isLt
   have hx (i:ℕ)(hi:i≤ n): u i= fun x=> M.splitting.part i n (F x):= funext fun x=> (at_row T r X w f p hi s h.1 x)
   have ht : Integrable F:= by
      rw [show F=(fun x=> ∑ j:Fin (n+1), L j (u j x)) from ?_]; exact integrable_finsetSum _ fun j _=> (L j).integrable_comp (he _ (hL j))
      funext x; exact (M.splitting.recombine M.hierarchy.laws.toSymmetric M.incl n (F x)).symm.trans (Finset.sum_congr rfl fun i _=> congrArg (L i) (congr_fun (hx _ (hL i)) x).symm)
   exact ⟨ht,fun i hi=> ((LinearMap.toContinuousLinearMap (M.splitting.part i n)).integral_comp_comm ht).symm.trans (integral_congr_ae (Eventually.of_forall fun t=> (congr_fun (hx i hi) t).symm))⟩
end Thresholds
end YM.Contacts.Solstice
