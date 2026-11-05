import YM.RG08.Carrel.Hood

/-! # Φ side receipts for local blocks and Haares. All in same units (coords may already be packed).
    Promote any relative-tape analytic symbol with finitely many charged parameters into shared
    Flake horizon ensuring strict arrows in positive moment cost.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Tack
open Camera Glyph Room Forms Lattice Laurent Pert.Bulk Isles Packets Finset Function MvPolynomial
open Carrel
open scoped BigOperators Classical ContDiff PowerSeries ENNReal Topology
variable {I J:Type}{P:Side}{n:ℕ}[Fintype I]

/-- View of a single slot on periodic cover with origin attached. -/
def glance (o:Site P)(pick:I→Market J):Strip I (Cove P J):=fun j f=> f (wrap P (pick j).1+o,(pick j).2)
omit [Fintype I] in
theorem glance_pace [Fintype J] (o:Site P)(pick:I→Market J)(j):Pace (glance o pick j):=contDiffAt_apply ..

def intake (n:ℕ)(f:Still I)(pick:I→Market J) (x: Slide J n):ℝ:=∑ y:Tape n I,if x=pick ∘ y then Camera.deck n f y else 0

lemma intake_zero (f:Still I)(pick:I→Market J)(x:Slide J n)(hh:x∉ Finset.univ.image (fun y:Tape n I=>pick ∘ y)):intake n f pick x=0:=by
 unfold intake;apply sum_eq_zero;intro y _;rw [if_neg];intro hy;rw [hy] at hh;exact hh (mem_image_of_mem _ (mem_univ y))

def price (n:ℕ)(σ:ℝ)(f:Still I)(pick:I→Market J):ℝ:=∑ y:Tape n I,|Camera.deck n f y| *Real.exp (σ*shelf (pick ∘ y))
lemma price_nn (σ)(f:Still I)(pick:I→Market J):0≤price n σ f pick:=Finset.sum_nonneg (fun _ _=> mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
lemma intake_won (σ)(f:Still I)(pick:I→Market J): Won (intake n f pick) σ (price n σ f pick):=by
 refine ⟨price_nn _ _ _,?_⟩
 calc
 Cost (intake n f pick) σ ≤ ∑' x:Slide J n, ∑ y:Tape n I,bill (if x= pick ∘ y then Camera.deck n f y else 0) (σ*shelf x) := ENNReal.tsum_le_tsum fun x=> bill_sum _ _
 _ = _:= by
   have he (S:Tape n I→ ENNReal):∑ y:Tape n I,S y=∑' y:Tape n I,S y:=(tsum_fintype _).symm
   simp_rw [he];rw [ENNReal.tsum_comm,tsum_fintype]; unfold bill
   unfold price
   rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
   apply Finset.sum_congr rfl; intro i _
   simp [apply_ite abs,ite_mul,apply_ite ENNReal.ofReal,tsum_ite_eq]

lemma enrolled (f:Still I)(pick:I→Market J)(o:Site P)(x:Cove P J→ℝ):
   (∑' s:Slide J n, intake n f pick s*per_use s x o)= MvPolynomial.eval (roll (glance o pick) x) (tap n (flask f)):=by
 simp_rw [intake,Finset.sum_mul,ite_mul,zero_mul]
 rw [Summable.tsum_finsetSum,flute,←deck_parley f,parley,eval_sum];simp_rw [tsum_ite_eq, MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,word,map_prod,eval_X];rfl
 intro j _;apply summable_of_ne_finset_zero (s:={pick ∘ j});intro x hx; exact if_neg (by simpa only [mem_singleton] using hx)

def trace (n:ℕ)(f:Still I)(pick:I→Market J):Flake n (Market J):=bleach (grown (intake n f pick))
theorem trace_bill (n:ℕ)(f:Still I)(pick:I→Market J){σ:ℝ}: Held (carpet J) σ (price n σ f pick) (trace n f pick) ∧ Sym (trace n f pick) ∧ Cohort (trace n f pick):= ⟨(grown_held (intake_won _ _ _)).bleach (price_nn ..),symmetric _,(grown_y _).clean⟩

 theorem bleaching {F:Flake n (Market J)}{σ p:ℝ}(h:Cohort F)(hh:Held (carpet _) σ p F)(ht:0≤σ)(i:Fin n):pour (P:=P) (bleach F) i=bleach (pour F i):=by
   have hs(e:Equiv.Perm (Fin n))(v:Tape n (Cove P J)) : Summable (fun x:↥(lantern i v)=> woven F e x.val):=by
      apply Summable.of_norm;exact ((cell_sum (hh.perm e) ht i (reach (v i))).comp_injective (Subtype.val_injective (p:=fun x=>x∈lantern i v))).congr (by intro x; rw [Function.comp_apply,if_pos x.property.1,Real.norm_eq_abs])
   unfold bleach
   have he : (fun a=>pour (P:=P) ((∑ e:Equiv.Perm (Fin n), woven F e)) i a)= ∑ e:Equiv.Perm (Fin n),woven (pour (P:=P) F i) e:=by
      ext v :1; rw [pour_at];simp_rw [Finset.sum_apply];rw [Summable.tsum_finsetSum (fun e _=>hs e v)]; apply Finset.sum_congr rfl;intro e _;rw [← pour_at,ordered _ _ _ h]
   ext v;rw [pour_at];simp_rw [Pi.smul_apply,smul_eq_mul,tsum_mul_left,←pour_at];rw [congrFun he]
-- reading generic J, Carrel.reading is color mix only.
variable [Fintype J]
lemma picture (i:Fin n)(f:Still I)(pick:I→Market J)(x:Cove P J→ℝ):
  eval x (parley (pour (trace n f pick) i))=∑ o:Site P, eval (roll (glance o pick) x) (tap n (flask f)):=by
  let F:=intake n f pick; let E:=price n 1 f pick
  have hh:Won F 1 E:=intake_won 1 f pick; have hu:= word_sum hh zero_le_one
  rw [trace,bleaching (grown_y _) (grown_held hh) (by norm_num), parley_clean] -- pour_bleach mix only
  unfold parley; rw [eval_sum];simp_rw [MvPolynomial.smul_eq_C_mul, eval_mul,eval_C,word,map_prod,eval_X]
  change (∑ s:Tape n _,pour (grown F) i s*_)=_
  rw [purchased F hu,per_sum];simp_rw [Finset.mul_sum];rw [Summable.tsum_finsetSum]
  simp_rw [F,enrolled]
  intro o _
  apply summable_of_ne_finset_zero (s:=Finset.univ.image (fun y:Tape n I=>pick ∘ y));intro z hz;rw [show F z=0 from intake_zero f pick z hz,zero_mul]
 end YM.RG08.Tack
