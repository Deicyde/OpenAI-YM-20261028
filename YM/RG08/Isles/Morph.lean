import YM.RG08.Isles.Pieces

/-! The analogous convergence for many lines. -/
noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I J:Type}{σ B:ℝ}
structure StudyCross (I J:Type)(σ B:ℝ)(g:(i:ℕ)→colony I i → colony J i→ℝ)(G:Kernel I J):Prop where
 rate : 0<σ
 cost : 0≤B
 near : ∀ x,∑' y,bill (G x y) (σ*sep x.1 y.1) ≤ ENNReal.ofReal B
 far : ∀ y,∑' x,bill (G x y) (σ*sep x.1 y.1) ≤ ENNReal.ofReal B
 low (m x) : ∑' y,bill (g m x y) (σ*walk x.1 y.1) ≤ ENNReal.ofReal B
 tall (m y) : ∑' x,bill (g m x y) (σ*walk x.1 y.1) ≤ ENNReal.ofReal B
 light (x y): Tendsto (fun i=>g i (port (chain i) x) (port (chain i) y)) atTop (𝓝 (G x y))

variable {G:Kernel I J}{g:(i:ℕ)→colony I i→colony J i→ℝ}
lemma StudyCross.line {g:(i:ℕ)→Forms.Line (colony I i)}{G : Kernel I I}(h:StudyCross I I σ B g G) : StudyLine σ B g G:=⟨h.rate,⟨h.rate.le,h.cost,h.near,h.far⟩,fun i=>⟨h.rate.le,h.cost,h.low i,h.tall i⟩,h.light⟩
lemma StudyCross.mono {σ' B':ℝ}(h:StudyCross I J σ B g G)(hi:0<σ')(he:σ'≤σ)(hq:B≤B'):StudyCross I J σ' B' g G:=by
 have hm {X} (f d:X→ℝ)(hd:∀ x,0≤d x)(h:∑' x,bill (f x) (σ*d x)≤ENNReal.ofReal B):∑'x,bill (f x) (σ'*d x)≤ENNReal.ofReal B':=(ENNReal.tsum_le_tsum fun x=>bill_mono le_rfl (mul_le_mul_of_nonneg_right he (hd x))).trans (h.trans (by gcongr))
 refine ⟨hi,h.cost.trans hq,fun x=>hm (G x) _ (fun _=>sep_nonneg ..) (h.near x),fun y=>hm _ _ (fun _=>sep_nonneg ..) (h.far y),?_,?_,h.light⟩ <;>
 intro m x
 · exact hm _ _ (fun y=> by unfold walk; positivity) (h.low m x)
 exact hm _ _ (fun y=>by unfold walk;positivity) (h.tall m x)
lemma StudyCross.point (h:StudyCross I J σ B g G)(i:ℕ)(x:colony I i)(y:Market J):
   |g i x (port (chain i) y)| ≤ B*Real.exp (σ*abroad y)*weightU σ (reach x) := by
 unfold weightU;rw [here];apply decay (d:= walk x.1 (port (chain i) y).1) ((ENNReal.ofReal_le_ofReal_iff h.cost).mp ((ENNReal.le_tsum (port (chain i) y)).trans (h.low i x))) h.rate.le h.cost
 let z:colony I i:=((port (chain i) y).1,x.2)
 have ht:native z=native (port (chain i) y):=rfl
 exact (region x z).trans (by rw [ht,add_comm]; exact add_le_add_left (native_port _) _)
-- weightU uses Fintype I? weight defined after [Fintype I] but def doesn't use infer? check
variable {n:ℕ}{f:ViewDeck n I}{F:Flake n (Market I)} {p:ℝ}
variable {Gm:Cables n (Market I) (Market J)}{gm:(i:ℕ)→Cables n (colony I i) (colony J i)}{q:Fin n→ℝ}
lemma cover_cross (H:∀ i,StudyCross I J σ (q i) (fun m=>gm m i) (Gm i))(hs:0≤σ):
    let E:Cables n (Market I) (Market J):=fun _ x y=>σ*sep x.1 y.1
    lighthouse (carpet I) (carpet J) σ σ E Gm ∧ street E Gm q:=by
 intro E
 refine ⟨⟨hs,hs,fun _ _ _=>mul_nonneg hs (sep_nonneg ..),?_⟩,fun i=>⟨(H i).cost,(H i).near,(H i).far⟩⟩
 intro i j _ a b x y _ _
 have he:=sep_triangle x.1 a.1 y.1;have hh:=sep_triangle a.1 b.1 y.1; rw [sep_comm x.1 a.1] at he
 change σ*sep _ _ ≤ _;unfold E carpet;nlinarith
lemma scene_cross (H:∀ i,StudyCross I J σ (q i) (fun m=>gm m i) (Gm i))(hs:0≤σ)(m:ℕ):
    let E:Cables n (colony I m) (colony J m):=fun _ x y=>σ*walk x.1 y.1
    lighthouse (shore (chain m) I) (shore (chain m) J) σ σ E (gm m) ∧ street E (gm m) q:=by
 intro E; refine ⟨⟨hs,hs,fun _ _ _=>mul_nonneg hs (by unfold walk; positivity),?_⟩,fun i=>⟨(H i).cost,(H i).low m,(H i).tall m⟩⟩
 intro i j _ (a:colony I m) b (x:colony J m) y _ _
 let u:colony J m:=(a.1,x.2);let v:colony J m:=(b.1,x.2)
 let S:=shore (chain m) J
 have he:=S.slope x u y;have hh:=S.slope u v y;rw [S.left x u] at he
 change σ*S.span x y ≤ σ*S.span u v+σ*S.span u x+σ*S.span v y
 nlinarith

variable [Fintype I][Fintype J]
omit [Fintype J] in
lemma cards_price (hs:0<σ): Summable (fun x:Tape n (Market I)=> ∏ i, weightU σ (x i)):=by
 let F (x:Market I):=weightU σ x
 have h(x:Market I):0≤F x:=(Real.exp_pos _).le
 have he:∑' x,ENNReal.ofReal (F x)≠ ⊤:=by rw [←ENNReal.ofReal_tsum_of_nonneg h (weightU_sum hs)];finiteness
 suffices hh:∑' x:Tape n (Market I), ∏ i,ENNReal.ofReal (F (x i))≠ ⊤ by
   exact (ENNReal.summable_toReal hh).congr fun x=>by rw [ENNReal.toReal_prod]; simp_rw [ENNReal.toReal_ofReal (h _)];rfl
 rw [all_Δ (a:=fun _:Fin n=>fun x=>ENNReal.ofReal (F x)), Finset.prod_const,card_univ,Fintype.card_fin];exact ENNReal.pow_ne_top he

omit [Fintype J] in
lemma Study.morph (h:Study σ p f F)(H:∀ i,StudyCross I J σ (q i) (fun m=>gm m i) (Gm i)) :
  Study σ (p*∏ i,q i) (fun m=>raft (gm m) (f m)) (raft Gm F):=by
 have hp(i):= (H i).cost
 obtain ⟨ha,hg⟩:= cover_cross H h.rate.le
 refine ⟨h.rate,mul_nonneg h.cost (prod_nonneg fun i _=> hp i), h.palm.raft h.cost ha hg,fun i=>(h.calm i).raft h.cost (scene_cross H h.rate.le i).1 (scene_cross H h.rate.le i).2,?_⟩
 intro hn y
 let K (i:Fin n):=q i * Real.exp (σ*abroad (y i)); have hk(i):0≤K i:=mul_nonneg (hp i) (Real.exp_pos _).le
 apply DCT ((carpetRoad I).cards n) (fun i x=>vat (gm i) (f i) _ x) (fun x=>vat Gm F y x) (fun x=> (p*∏ i,K i)*(∏ i,weightU σ (x i)))
 · intro x; unfold vat design;apply Tendsto.mul (h.light hn x)
   exact tendsto_finsetProd _ fun i _=>(H i).light (x i) (y i)
 · exact (cards_price h.rate).mul_left _
 · intro x; exact mul_nonneg (mul_nonneg h.cost (prod_nonneg fun i _=>hk i)) (prod_nonneg fun i _=>(Real.exp_pos _).le)
 apply Eventually.of_forall; intro m x
 unfold vat design
 rw [Real.norm_eq_abs,abs_mul,mul_assoc,Finset.abs_prod,←Finset.prod_mul_distrib]
 exact mul_le_mul ((h.calm m).plain h.cost h.rate.le hn x) (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>(H i).point ..)) (Finset.prod_nonneg fun _ _=>abs_nonneg _) h.cost
end YM.RG08.Isles
