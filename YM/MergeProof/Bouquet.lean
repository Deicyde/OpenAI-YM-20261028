import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Veranda
set_option autoImplicit false
noncomputable section
namespace YM.Merge
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Turn Greenbelt Match Refrain Daisy Charity
open Progress.DirectedRecipe
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {A ι B:Type}
-- common base, derivatives can superpose exactly.
structure Joins (a:A)(t:ι→ℝ)(f:A→ℝ→ℝ)(v:ι→A):Prop where
    base i : f (v i) 0=f a 0
    atx (p:A) : DifferentiableAt ℝ (f p) 0
    sell : HasSum (fun i=> t i*deriv (f (v i)) 0) (deriv (f a) 0)
namespace Joins
variable {x:A}{t:ι→ℝ}{f g:A→ℝ→ℝ}{v:ι→A}
lemma mul (h:Joins x t f v) (p:Joins x t g v) : Joins x t (f*g) v:= by
  let a i:= deriv (f i) 0; let b i:=deriv (g i) 0
  have hi i:deriv ((f*g) i) 0= a i*g i 0+ f i 0 *b i:=deriv_mul (h.atx i) (p.atx i)
  refine ⟨fun i=> congr_arg₂ (·*·) (h.base i) (p.base i),fun i=> (h.atx i).mul (p.atx i),?_⟩
  simp_rw [hi,p.base,h.base]; exact ((h.sell.mul_right (g x 0)).add (p.sell.mul_left (f x 0))).congr_fun fun i=>by unfold a b; ring
lemma constant (z:ℝ): Joins x t (fun _ _=> z) v:= by refine ⟨fun _=>rfl,fun _=> differentiableAt_const _,?_⟩; simp
lemma prod (p:Finset B)(l:B→A→ℝ→ℝ)(h:∀ b∈p, Joins x t (l b) v): Joins x t (∏ i∈p,l i) v:=by
  induction p using Finset.induction_on with
  | empty=> rw [Finset.prod_empty]; exact constant 1
  | @insert b p hp ih=> rw [Finset.prod_insert hp]; exact (h b (mem_insert_self _ _)).mul (ih fun b' hb=> h b' (mem_insert_of_mem hb))
lemma pow (h:Joins x t f v)(n:ℕ): Joins x t (f^n) v:=by
  induction n with
  | zero=> rw [pow_zero]; exact constant 1
  | succ n ih=> rw [pow_succ]; exact ih.mul h
lemma opposite (p:Joins x t f v): Joins x t (-f) v:= by
  convert ((constant (-1) (x:=x)).mul p) using 1; ext; simp
lemma frac (p:Joins x t f v)(u:ℝ): Joins x t (fun x i=> f x i/u) v:= by
  simp_rw [div_eq_mul_inv];exact p.mul (constant _)
end Joins
variable {G:Gauge}{c f:Side}{S:StepData c f}{I R: Rep G f} {P:Teller G} {F:Forest S.ratio}{T:Tube G S}
variable (M : Lotus.Leaf R) {μ α W C:ℝ}{L:Side}{Q: YM.ConnectedActivityE6.Target G P}{o:ConnectedActivityE6.Target.Order G W} (H : Cash W α μ L Q o C T R)
variable (χ:Chi)(U:Config G c)
structure Grouped (M:Lotus.Leaf R)(t:ι→ℝ)(N:ι→Lotus.Leaf R):Prop where
    turn i: (N i).turn=M.turn
    costs : Summable fun i=> ‖t i‖*(N i).weight
    earn V: HasSum (fun i=>t i*(N i).ingredient V) (M.ingredient V)
variable [Countable ι] {t:ι→ℝ}{M:Lotus.Leaf R}{N:ι→Lotus.Leaf R}
open Greenbelt Pond
namespace Grouped
include H
lemma hearth (g:Grouped M t N) (V:Coat T F) (k:Finset ℕ)(ht:V.x=α)(hx:V.width=o.K) (hV:V.manifest)(p:Molecule S):
   HasSum (fun i=> t i*(N i).tithe V k W o.a Q.table Q.halo p) (M.tithe V k W o.a Q.table Q.halo p):=by
  let W':=M.turn.badge S; let A:=(F.order G).prod V.dice
  let f0 (P:Lotus.Leaf R):= P.into V W o.a Q.table k Q.halo p
  have h(Z):= Lotus.Leaf.tip Z V k (show Cash W V.x μ L Q o C T R from ht.symm ▸ H) hx hV p
  let a q u:=t q*f0 (N q) u; have ha i:Integrable (a i) A:= (h (N i)|>.2.1).const_mul _
  have hv:= H
  have hG(p'): HasSum (fun i=>a i p') (f0 M p'):=by
     unfold a f0 Lotus.Leaf.into Lotus.Leaf.premium Lotus.Leaf.paidU Lotus.Leaf.fond
     simp_rw [g.turn]; split;next h=> simp only [← mul_assoc]; exact ((g.earn _).mul_right _).mul_right _
     next=> simp
  have he V: ∑' i,a i V=f0 M V:= (hG V).tsum_eq
  have hP:Summable (fun i=>∫ x,‖a i x‖ ∂A):=by
    let H': Cash W V.x μ L Q o C T R:=ht.symm ▸ H
    refine (g.costs.mul_right (if W'∈p then ∏ j∈p.erase W',H'.text j else 0)).of_nonneg_of_le (fun i=>integral_nonneg fun _=>norm_nonneg _) (fun i=>?_)
    unfold a; simp_rw [norm_mul, integral_const_mul]
    have hx:=h (N i)|>.2.2; rw [g.turn] at hx
    apply (mul_le_mul_of_nonneg_left hx (norm_nonneg (t i))).trans; dsimp only; split <;> ring_nf <;> exact le_rfl
  have hp:=hasSum_integral_of_summable_integral_norm ha hP
  simp_rw [he] at hp; unfold a at hp; simp_rw [integral_const_mul] at hp;exact hp
omit H
private lemma spill {A ι:Type}[Fintype A] {h:A→ι→ℝ}{t:ι→ℝ}{b:A→ℝ}(hp:∀ i, HasSum (fun j=> t j*h i j) (b i)): HasSum (fun i=>t i*likely (fun j=> h j i)) (likely b):=by
   refine (hasAvg (fun i j=> t j*h i j) b hp).congr_fun fun i=> ?_; rw [likely_mul]
include H
lemma stay (g:Grouped M t N) (V:Coat T F) (ht:V.x=α)(hx:V.width=o.K)(p:Molecule S): HasSum (fun i=> t i*(N i).bloom V W o.a Q.table Q.halo p) (M.bloom V W o.a Q.table Q.halo p):=by
   unfold Lotus.Leaf.bloom; split_ifs; · exact spill (fun i=> g.hearth H ((planted V p).taggedL i) _ ht hx (planted_valid ..) p)
   simp
lemma action (g:Grouped M t N) (p:Molecule S): HasSum (fun i=> t i*(N i).lotus T α χ o.K W o.a Q.table Q.halo U p) (M.lotus T α χ o.K W o.a Q.table Q.halo U p):= spill (fun i=>g.stay H (prism T α χ o.K U (allot i)) rfl rfl _)
local notation "C₁"=>fun M:Lotus.Leaf R=> color M H χ U
lemma galaxy (g:Grouped M t N)(p:Molecule S): Joins M t (fun M z=> C₁ M z p) N := by
   let f (X:Lotus.Leaf R) z:=color X H χ U z p
   let a (X:Lotus.Leaf R):= X.lotus T α χ o.K W o.a Q.table Q.halo U p
   have hp V:HasDerivAt (f V) (a V) 0:=by
     simpa [f,color,a] using (((hasDerivAt_id' (0:ℝ)).mul_const (a V)).const_add (H.spawn χ U p))
   change Joins M t f N
   refine ⟨fun i=> by simp [f], fun i=> (hp i).differentiableAt,?_⟩
   simp_rw [fun i=> (hp i).deriv]; exact g.action H χ U p
lemma flame (g:Grouped M t N)(p:H.fragrances): Joins M t (fun X z=> H.trainedMill ((C₁) X z) p) N:=by
   let f i (X: Lotus.Leaf R) z:= color X H χ U z (p.2 i).val; let F:= ∏ i, f i
   let c:=Ursell.coefficient H.seam p.2 -- edit
   have he : Joins M t F N:=Joins.prod Finset.univ f (fun i _=> g.galaxy ..)
   let f' (X: Lotus.Leaf R)(t:ℝ):= c*F X t/((p.1+1).factorial:ℝ)
   convert (Joins.frac ((Joins.constant c).mul he) (((p.1+1).factorial:ℕ):ℝ)) using 1;ext; simp [F,f,Cash.trainedMill,Gas.term,Cash.entriesMill,c]
lemma aroma (g:Grouped M t N)(p:H.Chapter):Joins M t (fun M z=> H.cologneMill (color M H χ U z) p) N:=by
   rcases p with p|p; exact g.galaxy H χ U p.val
   exact Joins.opposite (g.flame H χ U p)
lemma wheel (g:Grouped M t N)(p:H.Chainbook): Joins M t (fun M z=> H.smilesMill U (color M H χ U z) p) N:=by
   unfold Cash.smilesMill;split;next h=>
      let l i (x:Lotus.Leaf R) t:= H.cologneMill (color x H χ U t) ((i:↥(p.1)).val)^(p.2 i+1) /((p.2 i+1).factorial:ℝ)
      have hh:= Joins.prod Finset.univ l (fun i _=> ((g.aroma H χ U i.val).pow (p.2 i +1)).frac _)
      convert hh using 1; ext; simp only [l, Finset.prod_apply]; rfl
   next => exact Joins.constant _
lemma verses (g:Grouped M t N) (J:Cash W α μ L Q o C T I)(D:Alliance J H 1 0) (i:ℕ): Joins M t (fun M z=> veranda M H χ J D z i U) N:=by
   by_cases hv:i∈ Set.range (visa J D); unfold veranda
   · obtain ⟨z,rfl⟩:=hv; simp_rw [stuffed];exact g.wheel H χ U _
   unfold veranda; simp_rw [Progress.DirectedRecipe.blank _ _ hv]; exact Joins.constant _
end Grouped
end YM.Merge
