import YM.Next.RANK.Crust
import YM.Next.RANK.Dorics

/-!
# Local W kernel readings, restored transport paths
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset MeasureTheory
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q D N d : ℕ}
variable {f : Face (Per n)} {u : Site n} {B : ℕ}

theorem elude (b : ℕ) (x : Cover) (h : x∈box b) (i) : x+step i ∈ box (b+1):= (box_test).2 ⟨fun j=> by
  have hL:-(b:ℤ)≤ x j:= (box_test.mp h).1 _; simp only [Pi.add_apply,step_apply]; split <;> omega,fun j=> by
  have hh:x j≤ b:= (box_test.mp h).2 _; simp only [Pi.add_apply,step_apply]; split <;> omega⟩
private lemma box_widen {x : Cover} {B j} (h : x∈ box B) (H : B ≤ j) : x∈ box j:= box_test.mpr ⟨fun i=> by have := (box_test.mp h).1 i; omega,fun i=>by have:= (box_test.mp h).2 i; omega⟩

def ascentPatch (h : separation u f.1+2 ≤ B) : Turn B:= by
  let x:=lift (f.1-u)
  refine ⟨(x,f.2),Spindle.allowed _ ?_⟩
  intro i hi; rw [square_corners] at hi
  have hx:=Work.E08.lift_mem_box (show separation u f.1≤ B-2 from by omega)
  have hl:=elude _ x hx
  simp only [List.mem_cons, List.not_mem_nil,or_false] at hi; rcases hi with ht|ht|ht|ht|ht
  all_goals subst i
  · exact box_widen hx (by omega)
  · exact box_widen (hl _) (by omega)
  · exact box_widen (elude _ _ (hl _) _) (by omega)
  · exact box_widen (hl _) (by omega)
  exact box_widen hx (by omega)
lemma rotates (h : separation u f.1+2 ≤ B) (U : Config G n) (hp : 2*(B+1)<n.val):
    registered B U u (ascentPatch h)=faceValue (spine U u) f:= by
  rw [registering B U hp]; simp [ascentPatch]

def kiosk (c : ℝ) (u : Site n) (U : Config G n) (i : Face (Per n)) : G.Color := c⁻¹ • G.curvature (faceValue (spine U u) i)
lemma dotSize (c : ℝ) (hc : 0<c) {T : ℝ} (U : Config G n) (H : Healthy T (Spindle.patch B u) U) (hF : 2*(B+1)<n.val) (hp : separation u f.1+2 ≤ B) : ‖kiosk c u U f‖ ≤ T/c:= by
  rw [kiosk,← rotates hp U hF,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hc|>.le), ← div_eq_inv_mul]; exact div_le_div_of_nonneg_right ((G.curvature_norm _).trans (chords _ U T H hF _)) hc.le
lemma keyGauges (c : ℝ) (o : Site n) (V : Config G n) (f : Face (Per n)) (U) (H : separation o f.1+2≤B) (hx : 2*(B+1)<n.val) :
    kiosk c o (gauge U V) f=coloring (U o) (kiosk c o V) f:= by
  unfold coloring kiosk; rw [← rotates H _ hx,← rotates H _ hx, read_gauge, Gauge.curvature_conjugate, _root_.map_smul]
lemma keyPath (U : Face (Per n)) (o : Site n) (s : ℝ) : Continuous fun V : Config G n => kiosk (G:=G) s o V U := by
  let u (V : Config G n):=G.curvature (faceValue (spine V o) U)
  have hh : Continuous fun V : Config G n => faceValue (spine V o) U := by
    unfold spine; simp_rw [face_gauge]; unfold faceValue fingers leaves expandAt; fun_prop
  exact (continuous_const (y:= (s:ℝ)⁻¹)).smul (G.continuous_curvature.comp hh)

lemma taps_eq {ι : Type*} (P : Normal.poly ι) (X Y : ι→ℂ) (h : ∀ i∈P.vars,X i=Y i) : aeval X P= aeval Y P:= by
  obtain ⟨Q,hQ⟩:= trim_sigma P.vars P le_rfl
  let i:=rename (fun x:↥P.vars=> x.val) (R:=ℂ)
  have he : (aeval X).comp i=(aeval Y).comp i:= by ext x; simp [i,h x.val x.property]
  exact (congr_arg _ hQ.symm).trans ((show aeval X (i Q)= aeval Y (i Q) from DFunLike.congr_fun he Q).trans (congr_arg _ hQ))
lemma reads_eq {ι : Type*} (P : Normal.poly ι) (X Y : ι→ℝ) (h : ∀ i∈P.vars,X i=Y i) : text X P=text Y P:= taps_eq P _ _ fun i hi => congr_arg _ (h i hi)

def caseW (p : Normal.poly (bead G n)) (u : Site n) (c : ℝ) (U : Config G n) := text (rigid (kiosk c u U)) p
lemma case_meas (p : Normal.poly _) (c : ℝ) (u : Site n) : Continuous (caseW (G:=G) p u c):= by
  unfold caseW text; induction p using MvPolynomial.induction_on with
  | C i=> simp only [aeval_C]; exact continuous_const
  | add p q hp hq=> simp only [_root_.map_add]; exact hp.add hq
  | mul_X p i H=> simp only [_root_.map_mul,aeval_X]; apply Continuous.mul H; apply Complex.continuous_ofReal.comp; exact (EuclideanSpace.proj i.2.2 : G.Color →L[ℝ] ℝ).cont.comp (keyPath ..)
lemma case_in (P : Normal.poly (bead G n)) (hP : Poetic P) (c : ℝ) (H : ∀ i∈P.vars, separation u i.1+2 ≤ B) (hx : 2*(B+1)<n.val):
    LocalOn (Spindle.patch B u) (caseW P u c) ∧ GaugeInvariant (caseW P u c):= by
  constructor
  · intro U V h; apply reads_eq; intro i hi
    let f:= fromBead G i; have hQ : separation u f.1+2≤ B:= H _ hi
    unfold rigid kiosk; rw [← rotates hQ _ hx,← rotates hQ _ hx]; rw [show registered B U u (ascentPatch (f:=f) hQ)=_ from reads_face B u (ascentPatch hQ) U V h]
  intro k U
  unfold caseW
  rw [reads_eq P _ (rigid (coloring (k u) (kiosk c u U))) ?_,colours,hP]
  intro i hi; unfold rigid; rw [keyGauges c u U _ k (H i hi) hx]

-- gauged scale point at lift origin, before any amplitudes
lemma caseK (P : AtlasData G S p) (x : Cover) (j) (F : Normal.poly (slotC G k)) (h : 4*k≤l) (c : ℝ) (U) (hx : 2*(k+1)<(S.side j p).val) :
    caseW (lifted P F x j h) (wrap (S.side j p) x) c U = signet (wrap _ x) c F U:= by
  rw [primeVisit]; unfold caseW text signet
  let f:= kiosk c (wrap (S.side j p) x) U; let g:= curl k U c (wrap _ x)
  apply DFunLike.congr_fun (f:= (aeval _).comp (MvPolynomial.rename (position x))) (g:= (aeval _)); ext1 i
  rw [AlgHom.comp_apply,rename_X,aeval_X,aeval_X]
  unfold rigid Spindle.curl kiosk; dsimp only [Function.comp_apply]; rw [registering k U hx]
  change (↑((c⁻¹ • G.curvature _).ofLp i.2):ℂ)= _
  simp only [fromBead,position,map_add, add_comm (wrap (S.side j p) x)]
end YM.Next.Rank.Tapes
