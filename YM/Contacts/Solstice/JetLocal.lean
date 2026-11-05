import YM.Contacts.Solstice.Indemnity
/-!
# Only the indicated normal delta jets enter in the field channels

Taylor subtraction in the patch is field-local, not introducing further distributions along
higher strata. Equations in this file specify the sense of finite normal jets (when testing the
extension, not renormalized products of fields). Use also the relative-stage consistency later.
A convenient form is to *test* the correction, either using the same choices for all lower strata
and comparing two (convergent) versions of the root jet prescription, or testing the interior
pairings with corresponding vanishing jets. Even the entire **score** difference through the root
between such versions depends only on these jets & supplies solely the fields of the stated grades,
before integrating with other placement variables. In particular, in detecting any weight `w`, it
vanishes when tested with vanishing jets in **full normal directions** through the prescribed
order `K−w`. With fixed center and clearance from spectators, and lower choices held fixed, this
gives also the usual distributional criterion for a finite delta-jet change with these coefficients
when steering at weights `w`. The algebraic identity holds without convergence assumptions on the
other choices; to *test as distributions* comparing with another scheme one of course only does so
under the hypotheses in force there too (well-definedness of the two distributions). Not asserting
that all other Taylor prescriptions have these properties, nor that alternative choices are made in
the actual construction. In particular examples about comparing with a different choice in this file
always require a well-defined alternative to use between actual distributions. The construction uses
solely the field projection & apertures proved for our family. No terms at contacts derived from
higher-channel divergences below that horizon are left as undetected extra inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Solstice
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact MultipleContact.Script OPE Layers Ordered Harvest Route TopologicalSpace
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory TensorProduct
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X] [NormedSpace ℝ X][IsScalarTower ℝ ℂ X][CompleteSpace X]
variable {k : ℕ}{G:Gauge}{C:Family G}{Fi:Extraction.Order}{S:Table C.book}{Z:Final C Fi S}
variable {g : Normal.Group k}{P:E→ₗᵢ[ℝ] Points k}{d : Fin k→ℕ} (M : Devices Z.sector.derivatives)
local notation "E!"=> Expression Z.sector.derivatives
local notation "GN"=> Normal.Group k

def Flat (K:Submodule ℝ E) (n:ℕ) (x: SmoothTests E): Prop := ∀ y∈Kᗮ,∀ i≤n,∀ z∈K,(iteratedFDeriv ℝ i x.val y) (fun _=>z)=0
lemma flat_dep (t:ℝ){K:Submodule ℝ E}{m:ℕ}{x:SmoothTests E}(h:Flat K m x) : taylor K t m x=0 := taylor_jet_depend K t m (fun y hy x hx i hh=> h y hy i hh x hx)
omit [FiniteDimensional ℝ E] in
lemma Flat.lower {K : Submodule ℝ E}{n i : ℕ} (h : i≤n) {x: SmoothTests E}(ht:Flat K n x): Flat K i x := fun y hy j hj => ht y hy j (hj.trans h)

/-- State allowance of jet orders per weight, also when no projected candidates. -/
abbrev raised {k:ℕ}(d: Fin k→ℕ)(i : Normal.Group k) := Fin (levels d i)
def stencil {k:ℕ}(d:Fin k→ℕ)(i:Normal.Group k)(v:ℕ) := levels d i-1-v
structure Font (P:E→ₗᵢ[ℝ] Points k) (Z:Final C Fi S)(d:Fin k→ℕ) (i : Normal.Group k) where
  stroke : raised d i → Optical E
  vanishes (v:raised d i) {p : SmoothTests E} : Flat (normalOn P i) (stencil d i v.val) p → stroke v p=0
  -- outputs at the centroid in the same physical (unselected) filtration lift. Sign applied outside
  probe (v:raised d i) : E→ Expression Z.sector.derivatives→ₗ[ℂ] S.Field v.val

namespace Font
variable (F : Font P Z d g) (o : Points k)
def printed (Q : Score E (Expression Z.sector.derivatives))(v: raised d g) := reshape (fun x=> (insertField M.basis (centroid g (P x+o)) v).comp (F.probe v x)) Q * instructionScore E (Expression Z.sector.derivatives) (F.stroke v)
def wet (Q : Score E (Expression Z.sector.derivatives)) := - ∑ v,F.printed M o Q v
-- exactly the root modification in canonical formula. A different cutoff scale at this rank would change just stroke.
def present (d : Fin k→ℕ)(g : GN)(o : Points k)(P : E→ₗᵢ[ℝ] Points k)(s:ℝ): Font P Z d g where
  stroke i := taylor (normalOn P g) s (stencil d g i.val)
  vanishes _ _ hi:= flat_dep s hi
  probe v x:= M.row (centroid g (P x+o)) v

lemma font_rule (h : 1 < g.card)(s:ℝ)(c:Cells S d): (waySystem P M o d c).cumulant P s g= (present M d g o P s).wet M o ((waySystem P M o d c).punctured P s g):= by
   rw [System.equation_subtract _ _ _ _ h]; rfl
omit [FiniteDimensional ℝ E]
lemma wet_zero (h : levels d g= 0)(Q : Score E (Expression Z.sector.derivatives)) : F.wet M o Q=0:=by
   unfold wet; haveI: IsEmpty (raised d g):= ⟨fun i=>Nat.not_lt_zero _ (i.isLt.trans_le h.le)⟩; rw [Fintype.sum_empty,neg_zero]
lemma depend (v : raised d g){p:SmoothTests E} (hm : Flat (normalOn P g) (stencil d g v) p)(Q:Score E E!)(x:E) : action x p (F.printed M o Q v)=0:= by rw [printed,takeRight,F.vanishes _ hm]; exact map_zero (Normal.under _ _)
lemma reads (v : raised d g)(Q:Score E E!)(x:E)(p:SmoothTests E) : action x p (F.printed M o Q v)=insertField M.basis (centroid g (P x+o)) v (F.probe v x (action x (F.stroke v p) Q)) := by rw [printed,takeRight,action_reshape,LinearMap.comp_apply] -- using id right
lemma jet_alone {p:SmoothTests E} (hm : Flat (normalOn P g) (levels d g-1) p) (Q:Score E E!) (x:E) : action x p (F.wet M o Q)=0 := by rw [wet,map_neg,map_sum,Finset.sum_eq_zero (fun v _=> depend M F o v (hm.lower (Nat.sub_le ..)) Q x), neg_zero]
lemma float {n:ℕ} (v : raised d g)(p:SmoothTests E)(x:E)(hn : v.val < n)(Q:Score E E!) : M.row (centroid g (P x+o)) n (action x p (F.printed M o Q v))=0:=by rw [reads,M.row_of_field, M.splitting.beyondZero hn, LinearMap.zero_apply]
lemma flat_row {n:ℕ}(p:SmoothTests E)(hx : Flat (normalOn P g) (stencil d g n) p)(Q:Score E E!)(x:E) : M.row (centroid g (P x+o)) n (action x p (F.wet M o Q))=0:=by
    rw [wet,map_neg,map_sum,map_neg,map_sum,Finset.sum_eq_zero (?_),neg_zero]; intro v hv; by_cases he:v.val<n; exact float M F o v p x he Q; rw [F.depend M o v (Flat.lower (by unfold stencil; omega) hx),map_zero]
lemma past {n:ℕ}(h:levels d g≤n)(Q:Score E E!)(x:E)(p:SmoothTests E): M.row (centroid g (P x+o)) n (action x p (F.wet M o Q))=0:=by rw [wet,map_neg,map_sum,map_neg,map_sum,Finset.sum_eq_zero (fun v _=> float M F o v p x (lt_of_lt_of_le v.isLt h) Q),neg_zero]
/-- Readers see only centroid fields up to through K. -/
lemma unspent (Q:Score E E!)(x:E)(p:SmoothTests E) : action x p (F.wet M o Q)= ∑ v:raised d g, M.insertRow (centroid g (P x+o)) v (action x p (F.wet M o Q)):= by
    have hd(x':E!)(t:raised d g) (v:S.Field t.val) : (insertField M.basis (centroid g (P x+o)) t v)= ∑ v':raised d g,M.insertRow (centroid g (P x+o)) v' (insertField M.basis (centroid g (P x+o)) t v):= by
       let i:= levels d g-1; have h:t.val ≤ i:=by have ht:=t.isLt; omega
       let y:=insertField M.basis (centroid g (P x+o)) t v; change y=∑ v':raised d g,M.insertRow _ v' y; have he:i+1=levels d g:=by omega
       trans M.replaceAt (centroid g (P x+o)) i y; exact (M.replace_id (centroid g (P x+o)) h v).symm
       exact (M.replace_sum (centroid g (P x+o)) i y).symm.trans (congrArg (fun n:ℕ=> ∑ v':Fin n, M.insertRow (centroid g (P x+o)) v' y) he)
    rw [wet,map_neg,map_sum]; simp_rw [map_neg,map_sum,Finset.sum_neg_distrib]; apply congrArg Neg.neg; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun v _=> by rw [F.reads]; exact hd 0 v _

-- comparing relative versions at one rank of the induction with the PUNCT operations unchanged
variable (A: Font P Z d g)(T : Score E (Expression Z.sector.derivatives))
-- absolute only when comparing alternative extensions that work on the same placement space; no assumptions to be used in the construction about any other extension

def text (p:SmoothTests E)(x:E):=action x p (T+ F.wet M o T)
def climb (p:SmoothTests E)(x:E)(w:ℕ):= M.row (centroid g (P x+o)) w (F.text M o T p x)
lemma deltaFlat (w:ℕ){p:SmoothTests E}(ht: Flat (normalOn P g) (stencil d g w) p)(x:E): F.climb M o T p x w=A.climb M o T p x w:= by simp_rw [climb,text,map_add, ← map_add (centroid g) (P x) o]; rw [flat_row M F o p ht,flat_row M A o p ht]
lemma deltaOut (w:ℕ)(ht:levels d g ≤ w)(x:E)(p:SmoothTests E) : F.climb M o T p x w = A.climb M o T p x w:= by simp_rw [climb,text,map_add, ← map_add (centroid g) (P x) o]; rw [past M F o ht,past M A o ht]
/-- before testing with exteriors. Thus not tied to a phase and also applies for smearing in centroid. -/
lemma inside (p:SmoothTests E)(x:E) : F.text M o T p x-A.text M o T p x=
   ∑ v:raised d g, insertField M.basis (centroid g (P x+o)) v (F.climb M o T p x v-A.climb M o T p x v):= by
    unfold climb text; rw [map_add,map_add,add_sub_add_left_eq_sub] -- simp name
    simp_rw [map_add,add_sub_add_left_eq_sub,map_sub,Finset.sum_sub_distrib]; let g':= centroid g (P x+o)
    simp_rw [← map_add (centroid g) (P x) o]; exact congrArg₂ (· - ·) (F.unspent M o T x p) (A.unspent M o T x p) -- goal sum insertrow defeq?
-- fixed total normal stage conclusion after testing; state also between such actual working versions
variable [MeasureSpace E] [BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma emphasize (p:SmoothTests E) {e:E4}(hh : ∀ x:E, centroid g (P x+o)=e) (R : Expression Z.sector.derivatives →ₗ[ℂ] X)
      (hp : Integrable (fun x=>R (F.text M o T p x))) (hp' : Integrable (fun x=> R (A.text M o T p x)))
      (hm : ∀ v:raised d g, Integrable (fun x=> F.climb M o T p x v)) (hm' : ∀ v:raised d g, Integrable (fun x=> A.climb M o T p x v)): (∫ x,R (F.text M o T p x))-(∫ x,R (A.text M o T p x))=
      ∑ j:raised d g, R (insertField M.basis e j ( (∫ x,F.climb M o T p x j)-(∫ x, A.climb M o T p x j))) := by
    let V (j:raised d g):= LinearMap.toContinuousLinearMap (R.comp (insertField M.basis e j)); let t (j:raised d g)(x:E):=F.climb M o T p x j-A.climb M o T p x j
    rw [← integral_sub hp hp']; simp_rw [← map_sub, inside M F o A T,hh,map_sum]
    rw [integral_finsetSum ]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [← integral_sub (hm j) (hm' j)]; exact (V j).integral_comp_comm ((hm j).sub (hm' j))
    exact fun j _=> (V j).integrable_comp ((hm j).sub (hm' j))
end Font
end YM.Contacts.Solstice
