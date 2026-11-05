import YM.RG08.Pivot.Shame

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Finset
open scoped Topology BigOperators Classical
variable {A B C I : Type}[Fintype A][DecidableEq A][Fintype B][DecidableEq B][Fintype C][DecidableEq C]
variable {G: Gauge} {R:ℝ} {r d D j t e n: ℕ}{c f : Side}
lemma ordinary_σ {U : Screed ℝ A}{V : Canticle A}{P:Row A A}(S:Whole P)(hp:∀ i j,Tidy (U i j))(hV:Gets V)(o:Site c)(n r:ℕ): stitch (murmur (some c) P V U n 0 r) c o=terraces (P.acts c) (fun r=>stitch (U 0 r) c o) n r:= by
  have hg j k := (hV.2 j k).1
  induction n generalizing r with
  | zero=> rw [murmur,terraces]
  | succ n ih=>
    let F r:= murmur (some c) P V U n 0 r; have hh:= quiet_tidily S hg hp (some c) n 0 (r+2)
    have he : stitch (jib (some c) P (F (r+2))) c o=bur (P.acts c) (stitch (F (r+2)) c o) := Tensor.ext_diag _ _ ((jib_tidy hh.pens S _).sym _) (bur_sym _ (hh.sym o)) ((root_lap hh S c o).symm.trans (bur_lap (P.acts c) (hh.sym o)))
    rw [terraces, ← ih (r+2), murmur_step, Finset.sum_eq_zero,add_zero,st_scale _ ((jib_tidy hh.pens S _).pens.of_norm),show stitch (jib (some c) P (F (r+2))) c o=_ from he]
    intro i hi; refine sum_eq_zero fun a ha=> sum_eq_zero fun b hb=> ?_; have hx:= mem_antidiagonal.mp ha
    rw [show Refrain P V (some c) i.2 a.2 (b.2+1)= (0:Shale A (b.2+1)) from ?_, clasp_stop (quiet_tidily S hg hp _ _ _ _|>.pens) S,grant_zero]
    exact not_ne_iff.mp (fun hp=> by obtain ⟨⟨h,hh⟩,_⟩:= treble_reel S hg hV.1 hp; omega)
omit [DecidableEq A] in
lemma sym_weight {X:CupA A r} (hp:Tensor.Sym X) (a:ℝ): Tensor.Sym (a•X):=fun i j=>congr_arg (a • ·) (hp i j)
omit [DecidableEq A] in
lemma sym_pile (I':Finset I)(X:I→CupA A r)(hp:∀ i∈I',Tensor.Sym (X i)): Tensor.Sym (∑ i∈I',X i):= by
  intro i j; rw [_root_.sum_apply,_root_.sum_apply]; exact sum_congr rfl fun k hk=> hp _ hk i j
lemma twist_join (X:Matrix A B ℝ)(Y:Matrix B C ℝ)(V:CupA A r): twistV Y (twistV X V)=twistV (X*Y) V:= by ext1 v; simp_rw [twists,mulVec_mulVec]
lemma twist_seal {L:Quire.Rooted ℝ A r}(h:Tidy L) (o:Site c)(X: Row A B)(hp: Whole X): stitch (spring L X) c o = twistV (X.acts c) (stitch L c o) := by
    refine Tensor.ext_diag _ _ ((spring_tidy h.pens hp).sym _) (turns_sym _ (h.sym o)) (funext fun v=>?_)
    exact spring_tell _ h.pens hp o v
-- α costs all tall factors in kernel equation
variable {L:Side}{U:BoardU D R G}
def loomArc (g:Ratio c f): Matrix (Co f (Loc G 1)) (Co c (Park G g.count)) ℝ := LinearMap.toMatrix' (fineL G g).toLinearMap
lemma loom_tip (g:Ratio c f) (v:Alley G g): loomArc (G:=G) g *ᵥ v=fineL G g v := by rw [loomArc,LinearMap.toMatrix'_mulVec]; rfl
variable (g:Ratio c f) (ν:Site g.count)
def increase (L: Side)(d : ℕ):=(L.val:ℝ)^d /(Fintype.card (Site L):ℝ)
-- with G explicit
variable {p : Side} {S : Patch} {E : KernelChoices}{X : Repeated S.L} {w : Train S.J}{T:Air G}{b:G.ColorIndex}{Z:ChartRatio G} {M:Matrix (Body 1 f) (Body 1 c) ℝ}
def haloPull (p : Site L)(φ:Exam D):= Scores.Pages.roll (spinner p) (L.val:ℝ)⁻¹ φ
lemma sewn_rune {i:ℕ} (hV:1/2 ≤ R)(hp:Marvel n U) (h: Odd g.count.val)(o:Site c)(φ:Exam D) :
    stitch (plug φ R∘ cream t U g.count i r) c o=∑ p:Site g.count,increase g.count t • twistV (loomArc g) (recitalP (U i r) (g.assemble (o,p)) (haloPull p φ)) := by
  let e:= plug φ R; have he:=hp.hem i r
  apply Tensor.ext_diag _ _ ((Tidy.map _ ((creamy t g.count hp.cap (fun i j=>(hp.hem i j).pens) hV h).2 ..)).sym o)
    (sym_pile _ _ (fun j _=>sym_weight (turns_sym _ ((Tidy.map _ he).sym _)) _))
  funext x; unfold Tensor.diagonal; rw [_root_.sum_apply]; apply Eq.trans (cream_present g x o t i r φ he.pens hV h); apply sum_congr rfl; intro p _; rw [_root_.smul_apply,twists]; simp_rw [loom_tip]; rfl
lemma fil_layer {A β : Type} [Fintype A] [Fintype β] [DecidableEq A] [DecidableEq β]{K : Row A A}{S:Canticle A}{U:Screed (Voice D R) A}{F : Row A β}
    (h:∀ i j,Tidy (U i j))(hk:Whole K)(hp:Whole F)(hZ:Gets S)(m:ℕ)(o:Site c)(φ:Exam D):
    stitch (plug φ R ∘ spring (washed m (some c) K S U 0 r) F) c o= twistV (F.acts c) (harvestL (K.acts c) (fun i => stitch (plug φ R ∘ U 0 i) c o) m r):= by
    let q:=plug φ R; let V i j:=q∘U i j
    have hg i j: Tidy (V i j):=Tidy.map q (h i j)
    have ht i j:= (hZ.2 i j).1
    have hb:Tidy (washed m (some c) K S U 0 r):= Tidy.additions fun i _=> quiet_tidily hk ht h _ _ _ _
    rw [spring_echo _ hb.pens hp, twist_seal (Tidy.map _ hb) o F hp, wash_map _ hk ht h]
    unfold washed; rw [st_sums _ (fun i _=> (quiet_tidily hk ht hg (some c) i 0 r).pens.of_norm)]
    apply congr_arg (twistV _); unfold harvestL; rw [show windows m 0=m from by simp [windows]]; exact sum_congr rfl fun i _=> ordinary_σ hk hg hZ o i r
end YM.RG08.Pivot
