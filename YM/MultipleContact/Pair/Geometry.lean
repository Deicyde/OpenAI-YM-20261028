import YM.MultipleContact.Detector
import YM.MultipleContact.FieldBound
import YM.MultipleContact.Pair.Cost

/-! Translation conventions and exact detection at the center. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Two
open Function Extraction Filter Set Metric Table Power
open scoped Topology Filter BigOperators Classical ContDiff

variable {G:Gauge}{L:Register G}{S T:Table L}{n k w:ℕ}

def Room (K:Set (Points n)) : Prop:=∀z∈K,Points.cons 0 z∈conf _
def Safe (u:E4)(z:Points n) : Prop:= Points.cons u z∈conf _
lemma safe_zero {z:Points n}(hz:Points.cons 0 z∈conf (n+1)):Safe 0 z:=hz
lemma safe_pair {z:Points n}{x y:E4}(hx:Safe x z)(hy:Safe y z)(he:x≠y):Safe x (Points.cons y z):=by
   change Injective _; intro i j
   suffices ∀ i:Fin (n+1), x≠Points.cons y z i by
     exact Fin.cases (Fin.cases (fun _=>rfl) (fun j h=> (this j h).elim) j) (fun i=> Fin.cases (fun h=> (this i h.symm).elim) (fun j h=>congr_arg Fin.succ (hy h)) j) i
   exact fun i=> Fin.cases he (fun k=> by exact (hx.ne (Ne.symm (Fin.succ_ne_zero k)))) i
lemma continuous_cons : Continuous (fun x:E4 × Points n=> Points.cons x.1 x.2):=by
  refine (PiLp.continuous_toLp _ _).comp (continuous_pi (fun i=>?_))
  refine Fin.cases continuous_fst (fun j=>?_ ) i
  change Continuous (fun x:E4 × Points n=> x.2.ofLp j)
  fun_prop
lemma Room.reach {K:Set (Points n)}(h:Room K)(hK:IsCompact K):∃r:ℝ,0<r∧∀y∈ball (0:E4) r,∀z∈K,Safe y z:=by
   have he : ∀ᶠ y in 𝓝 (0:E4),∀z∈K,Safe y z:=hK.eventually_forall_of_forall_eventually fun z hz=> ((conf_open (n+1)).preimage continuous_cons).mem_nhds (h z hz)
   exact Metric.mem_nhds_iff.mp he

def relative (e:Exterior L):Points e.n := Points.across (-e.point 0) (Points.tail e.point)
private lemma relative_eq (e:Exterior L):Points.cons 0 (relative e)=Points.across (-e.point 0) e.point:=by
  ext1 i; exact Fin.cases (by simp [Points.cons]) (fun _=>rfl) i
lemma relative_safe (e:Exterior L):Safe 0 (relative e):=by unfold Safe;rw [relative_eq]; exact Points.across_in _ e.clear

def positions (u y:E4)(z:Points n):Points (n+2):=Points.cons (y+u) (Points.cons u z)
def half (y:E4):E4 := (2:ℝ)⁻¹ • y
def away (y:E4)(z:Points n):=positions (-half y) y z
def anchored (y:E4)(z:Points n):=positions 0 y z
lemma half_continuous : Continuous half := (continuous_id (X:=E4)).const_smul (2:ℝ)⁻¹
lemma half_norm (y:E4):‖half y‖≤‖y‖:=by unfold half; rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg y) (by norm_num)
lemma add_half (y:E4): y + -half y = half y:=by
   unfold half
   conv_lhs => lhs; rw [← one_smul ℝ y]
   rw [← neg_smul, ← add_smul]
   exact congr_arg (fun x:ℝ=>x • y) (by norm_num)
lemma away_as_cons (y:E4)(z:Points n):away y z=Points.cons (half y) (Points.cons (-half y) z):=by rw [away,positions,add_half]
lemma anchor_as_cons (y:E4)(z:Points n):anchored y z=Points.cons y (Points.cons 0 z):=by rw [anchored,positions,add_zero]
lemma anchored_clear {y:E4}(hy:y≠0){z:Points n}(h:Safe y z)(h':Safe 0 z):anchored y z∈conf _:=by rw [anchor_as_cons]; exact safe_pair h h' hy
lemma away_clear {y:E4}(hy:y≠0){z:Points n}(h:Safe (half y) z)(h':Safe (-half y) z):away y z ∈ conf _:=by unfold away positions; exact safe_pair ((Eq.symm (add_half y)) ▸ h) h' (left_ne_of_add_ne hy) -- fix
where
 left_ne_of_add_ne (a:y≠0) : y + -half y ≠ -half y:=fun eq=>a (add_right_cancel (by simpa only [zero_add] using (show y + -half y = 0 + -half y from eq.trans (zero_add _).symm)))

variable (T)(A B:S.Tag)(q:Fin n→L.Token)
private def inputs : Fin (n+2)→S.Tag := Fin.cons A (Fin.cons B (S.classTokens∘q))
def fixedValue (v:Fin n→S.Tag)(x:Points n) := S.useAt T x v
def anchoredValue (y:E4) (z:Points n):ℂ := fixedValue T (inputs A B q) (anchored y z)
def pairValue (y:E4) (z:Points n):ℂ := fixedValue T (inputs A B q) (away y z)
def siteValue (w:ℕ)(V:S.Field w)(u:E4)(z:Points n):ℂ:= fixedValue T (Fin.cons ⟨w,V⟩ (S.classTokens∘q)) (Points.cons u z)
lemma translate (h:T.Homogeneous) (v:Fin n→S.Tag)(z:Points n)(hz:z∈conf _)(u:E4):fixedValue T v (Points.across u z)=fixedValue T v z:=h n z hz u (fun i=> ⟨(v i).1,S.representative _ (v i).2⟩)

-- linearity in the output field.
lemma site_rep (h:T.Symmetric)(hr:T.respects S)(z:Points n)(u:E4)(hu : Safe u z)(w:ℕ)(v:S.Field w):siteValue T q w v u z=response T w (⟨n,Points.cons u z,q,hu⟩:Exterior L) v:= by
   exact (response_use (S:=S) ⟨T,⟨n,_,q,hu⟩⟩ h hr w v).symm

lemma site_orig (h:T.Homogeneous) (e:Exterior L)(w:ℕ)(v:S.Field w)(hT:T.Symmetric) (hr:T.respects S):siteValue T e.letter w v 0 (relative e)=response T w e v:=by
   rw [response_use (S:=S) (T,e) hT hr]
   unfold siteValue; rw [relative_eq (e:=e)]
   exact translate T h _ _ e.clear _

variable (w) (D:Detector S w)
def pull (g:∀e:Exterior L,E4→Points e.n→ℂ)(y:E4):S.Field w:= D.decode fun e:D.probes=>g e.val y (relative e.val)
def missAt (g:∀e:Exterior L,E4→Points e.n→ℂ)(e:Exterior L)(z:Points e.n)(y:E4):ℂ:=g e y z-siteValue S e.letter w (pull w D g y) 0 z
end YM.MultipleContact.Two
