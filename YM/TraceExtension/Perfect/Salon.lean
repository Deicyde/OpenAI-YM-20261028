import YM.TraceExtension.Perfect.Reckon

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge}
def landW (x:Site f)(j:pairA G f) := match j with
 | .inl j=>separation x j.1
 | .inr j=>separation x j.1
lemma lantern_arr (x:Site f):landW (G:=G) x=arranger x:=by funext i; cases i <;> exact separation_comm ..
variable (S:StepData c f)
local notation "K!"=>Cross S.ratio.count (TypeFace 1) (TypeFace 1)
def amber (W: K!)(x:Site f): pairA G f→pairA G c→ℝ:= doubling (palest (of (bloom S.ratio W x))) (palest 0)
def aquifer (W: K!)(x:Site f): pairA G f→pairA G c→ℝ:=doubling (palest (of (hingeQ S.ratio W x))) (palest (of (Perfect.trench S x)))
-- shape. Pre-L margins. pay eventually via choice
structure Glint (Z: Type)[Fintype Z] [DecidableEq Z] (v:Rays (pairA G c)→Rays Z) where
    h : True
variable {S}
lemma knit_fresh {g:StepData c f}{p : Clip}{M:PathData G}
   (F:Forest g.ratio) (ρ : Bid.Dir G c→AxisChart G F) (W:Matrix (Body 1 f) (Body 1 c) ℝ)(i:g.Choices)(z:Site f)
   (h:Critical F p M ρ)(hk:g.patch.Branches g.kernel G)(hx: Guessed F W ρ){u σ C :ℝ}(ht:M.Bounds p σ C u)(x : pairA G f)(y:pairA G c):
     fderiv ℝ (stampA g i (fresh F ρ W z)) 0 (desk y) x=quilt g (of (fleece W (g.ratio.count.val+1) z)) x y:=by
 refine knit (p:=p) (M:=M) _ _ i _ _ hk (fresh_thaw h _) (fresh_zero h _) ?_ (first_fresh h hk i hx z)
 let U : ℝ→ Stationary.Joint G c f:=fun _=>1
 exact (Stationary.awake (K:=1) i ht (U:=U) (Thaw.fixed 1 _) rfl hk root_customs).self_of_nhds

lemma sparkle (G:Gauge)(α η E T:ℝ)(t j:ℕ)(ha:0≤α)(h:α<η)(hT:0≤T)(hE:0 ≤ E):∃ C:ℝ,0 ≤ C ∧ ∀ (c f:Side)(S:StepData c f)(W: Cross S.ratio.count (TypeFace 1) (TypeFace 1)), S.patch.J=j →
    (∀ l:List Axis,l.length≤3 → (advanceC _ W l).strip η (E/(S.ratio.count.val:ℝ)^(1+l.length)))→
    8*(S.ratio.count.val+1)+4 ≤ f.val → ∀ v x, (separation (S.ratio.embed v) x:ℝ) ≤ T*S.ratio.count.val →
      Settle (landW v) (arranger x) (quilt (G:=G) S (of (fleece (installed S.ratio W) (S.ratio.count.val+1) x))) (amber S W x) (aquifer S W x) α t S.ratio.count.val C:=by
 obtain ⟨C,c,y⟩:= peg α η E T t ha h hE hT
 obtain ⟨B,b,u⟩:= polar_bud α T t j ha hT
 refine ⟨max C B,c.trans (le_max_left ..),fun c f S W hz hc hy v x hs=> ?_⟩
 have he := y _ _ _ W S.patch.odd_side hc hy v x hs
 have hw := u _ _ S hz v x hs
 -- equality of match
 have hh : landW (G:=G) v= Sum.elim (fun i: Lines G c 1=>separation v i.1) (fun i:Lines G c 1=>separation v i.1):=by funext i; cases i <;> rfl
 rw [hh]; apply doubling_pay _ _ _ _ (side_pos S.ratio.count) (skin_total _ _ _ _ _ _ he) (skin_total _ _ _ _ _ _ hw)

variable {I:Type}[Fintype I][DecidableEq I]{J:Type}[Fintype J]{N:ℕ}
lemma mono_sail (A:I→ℕ)(F:Rays I→ Rays J)(x:Rays I)(j:J)(α t r): sail F x A 1 j α t r = sh A α t r (fun b=> fderiv ℝ F x (desk b) j):=by
 unfold sail cost leaf bank; simp_rw [iteratedFDeriv_one_apply]; let E:= Equiv.funUnique (Fin 1) I
 have he (x : Fin 1→ I): limitN A x=A (x 0):=by simp [limitN];
 simp_rw [he]; exact E.sum_comp (fun b=> spot α t r (A b)* ‖fderiv ℝ F x (desk b) j‖)
end YM.Trace.Perfect
