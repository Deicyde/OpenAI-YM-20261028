import YM.TraceExtension.Anchor.PriceTest
import YM.Next.UV_STRESS.Value

/-! Test equivalence across fixed exteriors in the E table, using germ of positions
    of ONE anchor position, incl projection tests and for passing differences. `late` through
    subordinate filter, since holding field matrices for anchor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Function Filter Set MeasureTheory Analysis Extraction Around Table Ward Cells Lattice Wilson Next.UVStress
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} {D : ℕ}
section
variable (I:Watch C)
/-- Shift only the anchor mark away from centered Watch 0. -/
def rows (p : E4):= Points.cons p (Points.tail I.held)
lemma at_home : rows I 0=I.held := by
   unfold rows; ext1 i; refine Fin.cases ?_ (fun j=>?_) i
   · simp [Points.cons,I.origin]
   simp [Points.cons,Points.tail]

def plant (S : Table C.book) (d : ℕ) (p:E4): S.Field d →ₗ[ℂ] ℂ:= Work.A01.frontRead (S.classTokens ∘ I.q) (rows I p) d
lemma tester_home : plant I S D 0= I.tester S D:= by unfold plant; rw [at_home]; rfl
lemma testimonial (v : C.book.Token) (H:F.PointLimits C S) (k : ℕ)(x:Cover)(hp: rows I (C.S.gridPoint k x) ∈ generic _):
      Tendsto (fun i : ℕ × ℕ=> C.numeric i.1 i.2 (Fin.cons (α:=fun _=> C.book.Token) v I.q) (Fin.cons (α:=fun _=> Site (C.side i.1 i.2)) (location C.S k i.1 i.2 x) (I.among i.1 i.2))) F.fuse (𝓝 (S.read (rows I (C.S.gridPoint k x)) (Fin.cons (α:=fun _=> C.book.Token) v I.q))) := by
   let j:= max I.t k
   let hk := le_max_right I.t k; let hJ:= le_max_left I.t k
   let U := Fin.cons (α:=fun _=>Cover) (pushSite C.S hk x) (pushSite C.S hJ ∘ I.x); let W:=Fin.cons (α:=fun _=> C.book.Token) v I.q
   have he : rows I (C.S.gridPoint k x) = Extraction.Order.grid C j U := by
     unfold rows Extraction.Order.grid Points.cons
     ext1 i; refine Fin.cases ?_ (fun i=>?_) i
     · simp only [U,j,points_apply,Fin.cons_zero,finer]
     change _=C.S.gridPoint j (U (Fin.succ i)); unfold Points.tail Watch.held Watch.table Extraction.Order.grid; simp [U,finer]
   rw [he] at hp ⊢; refine (Extraction.Order.along (Cells.eventual_grid C F S H U hp W)).congr' ?_
   filter_upwards [large_mesh F j] with i hi; apply congr_arg (C.numeric _ _ W); ext1 l; refine Fin.cases ?_ (fun l=>?_) l
   · simp only [U,Fin.cons_zero]; exact location_down C.S hk hi x _
   simp only [U,Fin.cons_succ]; exact location_down C.S hJ hi _ _

lemma evaluates {b: Filter (ℕ×ℕ)} [b.NeBot](H:F.PointLimits C S) (hb:b ≤ F.fuse) (k : ℕ)(x:Cover)(hp: rows I (C.S.gridPoint k x) ∈ generic _) {v : ℕ×ℕ→ C.label D}{w:C.label D}(ht:Tendsto v b (𝓝 w)) :
      Tendsto (fun i:ℕ×ℕ=> C.numeric i.1 i.2 (Fin.cons (α:=fun _=> C.book.Token) ⟨D,v i⟩ I.q) (Fin.cons (α:=fun _=> Site (C.side i.1 i.2)) (location C.S k i.1 i.2 x) (I.among i.1 i.2))) b (𝓝 (S.read (rows I (C.S.gridPoint k x)) (Fin.cons (α:=fun _=> C.book.Token) ⟨D,w⟩ I.q))) := by
   let first (v : C.book.Token) := Fin.cons (α:=fun _=> C.book.Token) v I.q
   let seats (i:ℕ×ℕ):= Fin.cons (α:=fun _=> Site (C.side i.1 i.2)) (location C.S k i.1 i.2 x) (I.among i.1 i.2)
   let g (u : ℕ×ℕ):= C.ensemble (readDegrees (v:=I.q) D) (seats u)
   have hx (a:C.book.Ref D)(u:ℕ×ℕ) : C.numeric u.1 u.2 (first ⟨D,a⟩) (seats u)= g u (vals I.q a) := by
      rw [show first ⟨D,a⟩=(fun i => (⟨readDegrees (v:=I.q) D i,vals I.q a i⟩ : C.book.Token)) from ?_]; rfl
      funext i; refine Fin.cases (show first _ 0 = _ from (by rw [show first ⟨D,a⟩ 0=⟨D,a⟩ from Fin.cons_zero ..]; rfl)) (fun j => ?_) i
      unfold first; rw [Fin.cons_succ]; rfl
   let L (u : ℕ×ℕ) := LinearMap.toContinuousLinearMap
      (show C.book.Ref D→ₗ[ℂ] ℂ from (g u).toLinearMap (vals I.q (0:C.book.Ref D)) 0)
   have hy (a : C.book.Ref D) (u : ℕ×ℕ) : L u a = C.numeric u.1 u.2 (first ⟨D,a⟩) (seats u) := by
      rw [hx]; change g u (update (vals I.q (0:C.book.Ref D)) 0 (headValue I.q a))=_; rw [← update_front]
   have hz (a : C.book.Ref D) : Tendsto (fun u : ℕ×ℕ => (L u).toLinearMap a) b (𝓝 (S.injectFront I.q (rows I (C.S.gridPoint k x)) D a)) :=
      ((testimonial I ⟨D,a⟩ H k x hp).mono_left hb).congr fun u => (hy a u).symm
   exact (Dash.arcing (Dash.fit_plane (fun u => (L u).toLinearMap) (S.injectFront I.q _ D) hz) ht).congr (fun u => hy _ _)

variable (x : Cover)
lemma pitches {k N p : ℕ} (v:C.book.Token):
    let o:= location C.S k N p x
    C.numeric N p (Fin.cons (α:=fun _=> C.book.Token) v I.q) (Fin.cons (α:=fun _=> Site (C.side N p)) o (I.among N p)) = moment (C.beta N p) (fun U=> C.seen v 0 U * I.plot N p (translate (-o) U)) := by
   intro o; rw [C.num]
   let V:= Fin.cons (α:=fun _=> Site (C.side N p)) o (I.among N p)
   let W:= Fin.cons (α:=fun _=> C.book.Token) v I.q
   let P : Config G (C.side N p)→ℂ:= fun U=> ∏ j : Fin (I.n+1), C.seen (W j) (V j) U
   let f := fun U=> P (pull 1 (-o) U)
   have he: moment (C.beta N p) f=moment _ P:=moment_pull (C.beta N p) 1 (-o) P (C.integrableR ..)
   change _ = ∫ _, _∂law ..
   change moment (C.beta N p) P=_; rw [← he]; unfold f P; apply congr_arg (moment _); funext U
   rw [Fin.prod_univ_succ,pull_one]; simp only [W,V, Fin.cons_zero, Fin.cons_succ, Watch.plot]
   congr 1; change C.O N p _ o (translate (-o) U)=C.O N p _ _ _; rw [C.translation,add_neg_cancel]
end
end YM.Trace.Pull
