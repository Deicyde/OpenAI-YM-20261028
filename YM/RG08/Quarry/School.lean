import YM.RG08.Quarry.Puzzle

/-! # Unmarked vacuum laws on normalized announced. Unmatched e can use any gauges plus
 these sparse wedges.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Filter Function Matrix Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Slate Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Mount Glyph Room Rows Bloch
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {G : Gauge}
variable (P:Patch)(K:KernelChoices)(h:P.Branches K G)(A B:Bed)(C:Castle G)(Z:ChartRatio G)

-- Unchanged data sets from readers through Bore. No physical positive reports required.
structure Foyer where
 stash: Mount.Stable C
 gold:∃ σ p,0 < σ ∧ σ ≤ 1 ∧ Cell.Warm G K P A σ p
 shade:∃ τ u,0 < τ∧ τ ≤ 1∧ 0 ≤ u ∧ B.metric.strip τ u
 eye:LocalRatio Z
 budget: ∀ i,Proceed C A (Isles.chain i * P.L)
 hero : ∃ (a b:ℝ) (v:Clip), ∀ i,Floor A v (Isles.chain i*P.L) a b
 plan:∃ N:ℕ→ℕ,Tendsto N atTop atTop ∧ ∀ i:ℕ, ∃ L, Inputs (Line.habitat P K (Isles.chain (N i))) L (A.metric.acts (Isles.chain (N i)*P.L)) (B.metric.acts (Isles.chain (N i)))

lemma deliver {X Y:Side→Type}[∀i,Fintype (X i)][∀i,Fintype (Y i)](F:Foyer P K A B C Z)(x:∀ i:Side,Lines G i 1→X i)(y:∀ i:Side,Lines G i 1→Y i)(s t:Tray (Market (Loc G 1)))
    (hg:∀ᶠ n:ℕ in atTop, let i:=Isles.chain n
    ;∃ (W:Bore (Line.habitat P K i) (Line.green _) A B (x i) (y i) Z) (f: Heights (Line.habitat P K i) (Line.green _) G (X i)→Dig), (∀ q:Lines G i 1, breath f (rescaleFields W.map (.inr (y i q)))=(Gallery.native i t).get q) ∧ (∀ q,f (.inr (x i q))=(Gallery.native i s).get q)):
    announced (vault G P K h C Z A B) s=announced (vault G P K h C Z A B) t:=by
 obtain ⟨hC,⟨_,_,hy,hp,hx⟩,⟨_,_,he,hU,hB,ho⟩,hz,hs,⟨_,_,_,hf⟩,⟨N,hN,hL⟩⟩:=F
 choose L hL using hL
 apply Gallery.anchor (N:=Isles.chain ∘ N) (V:=fun i=>tray G P K h C Z A B (Isles.chain (N i))) _ (Isles.rise.comp hN)
 · filter_upwards [hN.eventually hg] with k hk; let i:=Isles.chain (N k); dsimp only at hk; obtain ⟨v,z,ht,hu⟩:=hk;
   exact (forming G P K h A B C Z (X:=X) (Y:=Y) i (x i) (y i) v hC hz (hs _) hx (hf _) (hL k) s t z ht hu).symm
 intro i n he1 z;exact (graft_vault G P K h C Z A B hC hx hy hp ho he hU hB _ _ he1 z).comp hN

def Academy (V:Gallery.Script (Market (Loc G 1))):Prop:=∀ (x:Tray (Market (Loc G 1)))(u:Tray (Market G.ColorIndex))(d:G.El),announced V x=announced V (portrait (hot d) (art x u))

lemma lectern (F:Foyer P K A B C Z): Academy (vault G P K h C Z A B):=by
 intro x u d
 let y:= art x u
 apply deliver P K h A B C Z (X:=fun c=>Cove c (cuff G)) (Y:=fun c=>Lines G c 1) F badge (fun _=>id)
 filter_upwards [rear (hot d) y Isles.rise] with n hn
 let c:=Isles.chain n;let S:=Line.habitat P K c; let F:=Line.green S
 let T:= route S F (badge (G:=G) c) (raise c d)
 rename_i F₀ -- shadows?
 let U:= Heights S F G (Cove c (cuff G));let f:U→Dig:=Sum.elim (fun _=>0) (Gallery.native c y).get
 refine ⟨certify S F A B _ _ _ _ T Z ?_,f,?_,?_⟩
 · exact F₀.eye
 · intro q
   change breath f (eye (fun t:Cellar U=> arch (badge c) (raise c d) (t ∘ Sum.inr) q))=_
   rw [prophet]; exact (hn q).symm
 intro i; rfl
lemma schools (V:Gallery.Script (Market (Loc G 1)))(h: Academy V)(e:ℕ): Gauged V e ∧ Sworn V e:=by
 have ht (r s:ℝ) (x:Demo (Mix G.ColorIndex 1))(z:Cover)(p:G.ColorIndex)(d:G.El):
    ∃ a b:Tray (Mix G.ColorIndex 1),(Demo.flat a).play=r • x.play ∧ ((Demo.flat b).play=fun i:Mix G.ColorIndex 1=>r* G.adjoint d (heavy G (fun l=>(x.play+s • (bolt z p).play) (i.1,i.2.1,l))) i.2.2) ∧ tap e (announced V a)=tap e (announced V b):=by
     refine ⟨pend r x,portrait (hot d) (art (pend r x) (diver (r*s) (z,p))),funext fun i=> ?_,funext (fun i=>puzzle d r s x (z,p) i),congrArg (tap e) (h ..)⟩;
     simp [Demo.flat,pend,Demo.pump,Demo.reals]
 constructor
 · intro x r s z p
   obtain ⟨a,b,ha,hb,he⟩:=ht r s x z p 1
   refine ⟨a,b,ha,?_,he⟩;rw [hb]; simp only [Gauge.adjoint_one]; rfl
 intro d x r
 by_cases hem:Nonempty G.ColorIndex
 · obtain ⟨q⟩:=hem;obtain ⟨a,b,ha,hb,he⟩:=ht r 0 x 0 q d; refine ⟨a,b,ha,?_,he⟩;rw [hb];simp only [zero_smul,add_zero];rfl
 haveI : IsEmpty G.ColorIndex:=not_nonempty_iff.mp hem
 exact ⟨pend r x,pend r x,funext (fun ⟨_,_,i⟩=> isEmptyElim i),funext (fun ⟨_,_,i⟩=> isEmptyElim i),rfl⟩
end YM.RG08.Quarry
