import YM.WilsonBulk.Cash.Warm

/-!
# Exact same-rank input-coupling port and remainder coat
    estimates apply at all orders ≥1 (Atelier tape precision) & rank≥1 not requiring value. Tested
    within actual QR21 heights, consumed polynomial couplings Age etc later. `coat` cannot include rank0 scalar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {X Y : Type} {n k e E d : ℕ} {σ μ θ η ζ x A M q δ : ℝ}
variable {P : Patch} {K : KernelChoices} {J : ChartRatio G} {T : Model P K} {l : G.ColorIndex}
variable {V U : Bed} {B Q B' Q' : Bed} {I I' : Library G} {D D' : Shaft P.L}
abbrev primer (P : Patch) (K : KernelChoices) (J : ChartRatio G) := lecture (oil G P) (curtainHair J)-noisePart P K G
lemma dais_split (I : Library G) (P : Patch) (K : KernelChoices) (J : ChartRatio G) : dais J P K I=primer P K J - lecture (oil G P) (later I) := rfl
def coat (T : Model P K) (B : Bed) (J : ChartRatio G) (I : Library G) := primer P K J + (heating J T B I-dais J P K I)
def strictMap (T : Model P K) (B : Bed) (J : ChartRatio G) (I : Library G) := lecture (plain (pilot (G:=G) T B)) (coat T B J I)

-- exact structural expression. Also used for actual period bridges at charge≥1 elsewhere.
lemma blend_prim (I : Library G) (P : Patch) (K : KernelChoices) (J : ChartRatio G) (h : 0<e) (T : Model P K) (B : Bed) :
    heating J T B I e k=coat T B J I e k-lecture (oil G P) I e k := by
  unfold coat; rw [dais_split]; simp only [Pi.add_apply,Pi.sub_apply]; simp only [lecture,later,switchBoard,if_pos h.ne']; abel
lemma prism_engaged (h : Tarmac l J T B Q D θ σ μ x q E A) (he : Pamphlet I) (hp : 0<e) : Public (coat T B J I e (n+1)) := by
  rw [show coat T B J I e (n+1)=heating J T B I e (n+1)+lecture (oil G P) I e (n+1) from (eq_sub_iff_add_eq.mp (blend_prim I P K J hp T B)) |>.symm]
  let D:= cascade (1:Side); have ht:= cascade_up (c:=(1:Side)); let C:=cargo (G:=G) T B
  refine Public.plus (?h1) ((he _ _).travel (oilSession _ _ _) (fun b=>P.L.val • b) (fun a b c=> install_roll ..))
  · have hh := (dean.reached C (dais J P K I) D ht (fun i=>Sheet.issue (D i) (dais J P K I)) (fun e n _=>(podium_hears J P K he e n).forever D) h.warm.era.horizonM (corridor_height h.curtain.width (zero_le_one.trans h.warm.height)) (zero_le_one.trans h.warm.height) e (n+1) (by omega)); exact hh.claim _
-- tele composition oil->pilot
lemma sent_ruling_aux (g : Ratio c f) (W : Pace g.count G) (x : Pennant G f) (y : Pennant G c) :
    ∑ j, installed g (varnish g.count (Cloth G) (Cloth G)) x j * (efferos W).acts c j y= installed g W x y := by
  rw [← Equiv.sum_comp (promenade (Cloth G) (Cloth G) g)]; simp only [Fintype.sum_sum_type,varnish_at,varnish_not,ite_mul,one_mul,zero_mul, Finset.sum_const_zero,add_zero,sum_ite_eq,if_true,mem_univ]
  exact rfl
lemma sent_ruling (W : Pace P.L G) (hp : Lighthouse W) (V : Text (Cloth G) (n+1)) (h : Public V) (K : KernelChoices) : Sheet.travel (plain (efferos W)) (Sheet.travel (oil G P) V)=Sheet.travel (install W) V := by
  let D:=cascade (1:Side); let O:=oil G P
  let x (i : Fin (n+1)):= W; let U (i : Fin (n+1)):= varnish P.L (Cloth G) (Cloth G); let Y (_ : Fin (n+1)):= efferos W; have he : Plaza U:= plaza fun _=> ⟨1,one_pos,1,zero_le_one,varnish_cost _ _⟩
  obtain ⟨p,hh,M,hM,hW⟩:= hp; have hk : Plaza x:=⟨p,hh,M,hM,fun _=> hW⟩; have hr : Plaza Y:= plaza fun _=> ⟨p,hh,(max M 1),hM.trans (le_max_left ..), effer_cost W hW⟩
  change tele (plain ∘ Y) (tele (install ∘ U) V)=tele (install ∘ x) V
  refine coupon_high (D:=D) cascade_up ((h.orient he).ascend hr) (h.orient hk) (Eventually.of_forall fun i=>?_) ; let S:= draftAt P K (D i); erw [ascend_coupon (h.orient he) hr,orient_coupon S.ratio h he,orient_coupon S.ratio h hk]; apply tele_through; intro i a b
  exact sent_ruling_aux (g:=S.ratio) W a b

lemma garnish (h : Tarmac l J T B Q D θ σ μ x q E A) (hi : Pamphlet I) (hp : 0<e) : pressureI J T B Q I e (n+1) = lecture (install (beams G T B)) I e (n+1) - strictMap T B J I e (n+1) := by
  have hx := h.warm.era.horizonM; have hH:= h.arise; have he := h.warm.height
  let R := pilot (G:=G) T B; let P' (_:Fin (n+1)):= R; have hR : Plaza P':=plaza fun i=> ⟨μ,hx,max A 1,le_max_of_le_left (zero_le_one.trans he),effer_cost _ hH⟩
  have hs : Pamphlet (lecture (oil G P) I) := fun d n=> (hi d n).travel (oilSession G P n) (fun i=> P.L.val • i) (fun a b c=> install_roll ..)
  unfold pressureI strictMap wreath; simp only [Pi.sub_apply]; rw [summit, usher_else _ _ _ _ _ (Or.inr (by omega)), zero_sub,lecture,blend_prim _ _ _ _ hp, show Sheet.travel (plain (pilot (G:=G) T B)) _=_ from lantern_sub (plainMeet hR) (prism_engaged (n:=n) h hi hp) (hs e (n+1))] -- P'= rank constant instance
  unfold lecture; rw [show tele _ (Sheet.travel (oil G P) _)=_ from sent_ruling (beams G T B) ⟨μ,hx,A,zero_le_one.trans he,hH⟩ (I e (n+1)) (hi _ _) K, neg_sub]; rfl

end Parapet
end YM.WilsonBulk
