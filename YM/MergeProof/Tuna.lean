import YM.MergeProof.Bouquet
import YM.MergeProof.Buys
import YM.MergeProof.Gallery


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge   Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories
variable (T:GaugeDoor R E) (q:ι→ Lotus.Leaf R)
def Tunes (T:GaugeDoor R E):Prop:=∀ (ι:Type)[Countable ι] (M:Lotus.Leaf R)(q:ι→ Lotus.Leaf R)(t:ι→ℝ), Grouped M t q→ ∀ j U,HasSum (fun i=> t i*T.hinge (q i) j U) (T.hinge M j U)
-- Countable symbols.Merge infinite alignment
variable [Countable ι]
variable (t:ι→ℂ)(z:Wing)(h:∀ i,(q i).turn=z)
variable {d e B':ℝ}
local notation "ℓ"=> load
-- fuse any real weights.
variable (y:ι→ℝ)
include h
lemma squash [Nonempty ι] (hz: Summable (fun i=> ‖y i‖*(q i).weight)) :∃ M: Lotus.Leaf R, Grouped M y q∧ M.turn=z ∧ M.weight=∑' i,‖y i‖*(q i).weight:=by
   let p := ∑' i, ‖y i‖*(q i).weight; let f i U:= y i*(q i).ingredient U; let F U:=∑' i,f i U; let a:ι:=Classical.arbitrary ι
   have hp i: UsesFinal R.p.threshold (z.support R) (f i):=fun U V hx ht=> congr_arg (y i *·) ((q i).scopedR U V ((h i).symm ▸ hx) ((h i).symm ▸ ht))
   have hh(i U): ‖f i U‖ ≤ ‖y i‖*(q i).weight:= by unfold f; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((q i).earn U) (norm_nonneg _)
   have hs U: Summable (fun i=> ‖f i U‖):=hz.of_nonneg_of_le (fun i=> norm_nonneg _) (fun i=> hh i U)
   let M : Lotus.Leaf R:= { turn:=z
                            weight:=p
                            ingredient:=F
                            scopedR:=fun U V hx ht=> tsum_congr fun i=> hp i U V hx ht
                            grant:=fun U hu=> of_not_not (fun he=> hu ((tsum_congr fun i=>show f i U=0 from Classical.byContradiction fun h' => he ((h i) ▸ (q i).grant U (right_ne_zero_of_mul h'))).trans tsum_zero))
                            earn:=fun U=>(norm_tsum_le_tsum_norm (hs U)).trans ((hs U).tsum_le_tsum (fun i=> hh i U) hz)
                            borel:= Measurable.tsum fun i=> ((q i).borel.const_mul (y i))
                            blank:=(h a) ▸ (q a).blank
                            glows:=fun g U=> tsum_congr fun i=> congr_arg (y i *·) ((q i).glows g U) }
   exact ⟨M,⟨h,hz,fun U=>(hs U).of_norm.hasSum⟩,rfl,rfl⟩
-- upper support curtain candidate saturated.L
omit h
variable {q} {m:StepData c f} {M: Lotus.Leaf R}
-- Summability weighted profiles. ForceCost implies dominated. use grouping.W
lemma priced (h: SoundDoor m T)(hp:Summable fun i=> ‖t i‖*load (q i)) : ∀ U, Summable fun x:ι×ℕ=> ‖t x.1‖* ‖T.hinge (q x.1) x.2 U‖:=by
   intro U; obtain ⟨c,hc⟩:=h.volume; choose f hf hF using fun i=> hc (q i)
   let v(i:ι×ℕ):= E.p.mass (E.activities.forced i.2).support (f i.1 i.2)
   have hW:Summable fun i:ι×ℕ=> ‖t i.1‖*v i:=by
      apply (summable_prod_of_nonneg (fun i : ι×ℕ=> show 0 ≤ ‖t i.1‖*v i from mul_nonneg (norm_nonneg _) ((hf i.1).1 i.2))).2
      have hh: Summable (fun i=> ‖t i‖*(c*load (q i))):= (hp.mul_left c).congr fun i=> mul_left_comm ..
      have he(i):SumBudget (fun j=> ‖t i‖*v (i,j)) (‖t i‖*(c*load (q i))):= Extra.Multi.Budget.scale (hf i) (norm_nonneg _)
      exact ⟨fun i=>(he i).2.1,hh.of_nonneg_of_le (fun i=> tsum_nonneg (he i).1) (fun i=>(he i).2.2)⟩
   refine hW.of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
   let x':= T.hinge (q i.1) i.2 U
   rw [← Complex.norm_real x']; exact ((hF i.1 i.2).2 U).trans (E.p.loMass _ _ (hF i.1 i.2).1)
lemma tables (ht:Grouped M y q)(hT:Tunes T)(hv:SoundDoor m T)(p:Box c)(U:Config G c): HasSum (fun i=> (↑(y i):ℂ)*quoted T (q i) p U) (quoted T M p U):=by
   let v:= {i// barcode E.activities i=p}; let y' (i:ι):ℂ:= ↑(y i); let f(a : ι×v):= y a.1*T.hinge (q a.1) a.2.val U
   have hz:Summable (fun i=> ‖y' i‖ *load (q i)) := by
      unfold load BudgetPoint.mass Lotus.Leaf.crest; simp_rw [ht.turn]; refine (ht.costs.mul_left (Real.exp (R.p.supportExponent*coverNumber R.p.B M.crest))).congr ?_; intro b; unfold y'; rw [mul_left_comm, Complex.norm_real (y b)]
   have hs:Summable (fun p:ι×ℕ=> ‖y p.1‖*‖T.hinge (q p.1) p.2 U‖):= by simpa only [y',Complex.norm_real] using priced T y' hv hz U
   have hF:Summable f:=by apply Summable.of_norm; unfold f; simp_rw [norm_mul]; exact hs.comp_injective (i:=fun i:ι×v=> (i.1,i.2.val)) (fun i j e=> Prod.ext (Prod.mk.inj e).1 (Subtype.ext (Prod.mk.inj e).2))
   have he(i): (∑' a : v, (↑(f (i,a)):ℂ)) = y' i * quoted T (q i) p U:=by
      simp_rw [f,Complex.ofReal_mul,tsum_mul_left];rfl
   have hc(j:v):HasSum (fun i:ι =>(↑(f (i,j)):ℂ)) (↑(T.hinge M j.val U):ℂ):=Complex.ofRealCLM.hasSum (hT ι M q y ht j.val U)
   have hu: Summable (fun i=> (↑(f i):ℂ)):= Complex.ofRealCLM.summable hF
   have hz := hu.prod.hasSum
   have hZ: ∑' i : ι,∑' j:v,(↑(f (i,j)):ℂ)= quoted T M p U:= by rw [hu.prod_symm.tsum_comm]; simp_rw [(hc _).tsum_eq];rfl
   rw [← hZ]; exact hz.congr_fun (fun i=> (he i).symm)
end YM.MergeProof.Menu
