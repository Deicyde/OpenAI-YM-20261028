import YM.RG08.Hatch.Nest
import YM.RG08.Cairn.Book
 import YM.RG08.Prism.Egg

/-! # Packing and pulling from a root, same address transfers separately.
Theorem exact composition even @wrapped overlap for perturbed z.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Hatch
open Jetty Skiff Isles Forms Pert.Bulk Lattice Function Finset Laurent Filter Packets
open Tack RG Wilson Precision Stationary Bloch Room Gallery Camera MvPolynomial Glyph
open scoped Topology BigOperators PowerSeries ENNReal Classical
variable {I J U:Type}{d n l:ℕ}{F:Pack n I}{σ C:ℝ}{h:0<σ}{L:Loom I}{K:Loom J}

lemma moving_inj (u:I→J)(hu:Injective u):Injective (fun t:Tape n I=>u ∘ t):=fun _ _ he=>funext fun i=>hu (congrFun he i)
lemma b_here (u:I→J)(hu:Injective u)(x:Tape n I):broom u F (u ∘ x)=F x:=by
 funext f;unfold broom;simp_rw [(moving_inj u hu).eq_iff];exact tsum_ite_eq' ..
lemma b_away (u:I→J)(x:Tape n J)(he:¬∃ t:Tape n I,u ∘ t=x):broom u F x=0:=by
 funext f; unfold broom;push Not at he;simp [fun (i:Tape n I)=>Ne.symm (he i)]

lemma b_camp {R:Type}[AddCommMonoid R][TopologicalSpace R](u:I→J)(hu:Injective u)(f:Tape n J→NoteX→R)(hf:∀ x,f x 0=0):
    (∑' x:Tape n J,f x (broom u F x))=(∑' i:Tape n I,f (u ∘ i) (F i)):=by
 let z:=fun t:Tape n I=>u ∘ t; have hz:=moving_inj (n:=n) u hu
 let b(x:Tape n J):R:=f x (broom u F x)
 have he : Function.support b ⊆ Set.range z:=by
    intro i hi; by_contra! H; exact hi (by unfold b;rw [ b_away u i H,hf]) -- tactics
 change (∑' x,b x)=_
 rw [← tsum_subtype_eq_of_support_subset he,tsum_range _ hz];exact tsum_congr fun i=>by unfold b;rw [b_here u hu]
lemma b_broom (u:I→J)(w:J→U)(hu:Injective u):broom w (broom u F)=broom (w ∘ u) F:=by
 ext1 x;funext f
 unfold broom; change (∑' i:Tape n J,if x=w ∘ i then broom u F i f else 0)=_
 rw [b_camp (F:=F) u hu (fun i M=> if x=w ∘ i then M f else 0) (by simp)];rfl
lemma b_afford (u:I→J)(hu:Injective u){τ a:ℝ}(k:0<τ)(ht:τ≤σ)(ha:0≤a)(he:∀ i,τ*K.height (u i)≤σ*L.height i+a)(hp:Sings L d h F C):Sings K d k (broom u F) (Real.exp a * C):=by
 unfold Sings gems
 rw [b_camp (F:=F) _ hu (fun x P=> purse d k P*weft K τ x) (by simp [purse_zero])]
 calc
  _ ≤ ∑' i:Tape n I,ENNReal.ofReal (Real.exp a)*gems L d h F i:= ENNReal.tsum_le_tsum (fun i=>?_)
  _ ≤ _:=by rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.tsum_mul_left];gcongr;exact hp
 rw [gems,mul_left_comm]
 apply mul_le_mul' (purse_up _ ht _ le_rfl)
 unfold weft; rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
 rw [mul_comm τ,←le_div_iff₀ k];apply K.racks _ (by exact div_nonneg (add_nonneg ha (mul_nonneg h.le (L.cage_nn _))) k.le); intro j
 rw [le_div_iff₀ k,mul_comm]; refine (he (i j)).trans ?_;rw [add_comm];gcongr; exact L.float i j

-- packing map literal, no summability issues
variable {G:Gauge}{c f:Side}(P:Patch)(o:Site P.L)
def door (i:Market (Loc G 1)):Market (Tack.Head P G):= let v:=i.1+lift o; (rent P.L v,.inl (wrap P.L v,i.2))
lemma step_door:Injective (door (G:=G) P o):=by
 intro x y he; let z(i:Market (Loc G 1)):Market (Co P.L (Loc G 1)):= (Cell.column P.L (Loc G 1)).symm (i.1+lift o,i.2)
 have h:z x=z y:= Prod.ext (show (door P o x).1=_ from congrArg Prod.fst he) (Sum.inl.inj (show (door P o x).2=_ from congrArg Prod.snd he))
 have hx:= (Cell.column P.L (Loc G 1)).symm.injective h
 obtain ⟨x,p⟩:=x;obtain ⟨y,q⟩:=y; exact Prod.ext (add_right_cancel (congrArg Prod.fst hx)) (have ht:=congrArg (fun i:Market (Loc G 1)=>i.2) hx;ht)
lemma height_door (i:Market (Loc G 1)):abroad (door P o i) ≤ abroad i/(P.L.val:ℝ)+12:=by
 let f(x:Cover):Market (Co P.L (Loc G 1)):= (Cell.column P.L (Loc G 1)).symm (x,i.2)
 have he:(f 0).1=0:=by change rent P.L (0:Cover)=0; convert rent_lift (0:Site P.L); ext1 j; simp [Lattice.lift] -- lemma
 have hc:=Cell.separation_to (f (i.1+lift o)) (f 0)
 simp only [f,Equiv.apply_symm_apply] at *
 change length (rent P.L (i.1+lift o)-rent P.L 0) ≤ length ((i.1+lift o)-(0:Cover))/(P.L.val:ℝ)+8 at hc
 change rent P.L (0:Cover)=0 at he;rw [he,sub_zero,sub_zero] at hc
 have ht:=length_lift P.L o; have hv:0<(P.L.val:ℝ):=by positivity
 have hJ : length (i.1+lift o) ≤ length i.1+length (lift o):=length_add _ _
 change length (rent P.L (i.1+lift o)) ≤ length i.1 /_+12
 have hs:=div_le_div_of_nonneg_right hJ hv.le;rw [add_div] at hs; linarith only [ht,hc,hs]
-- literal finite address seek displacement = +lift o; cylinders pinned at translated root later
variable (M:KernelChoices)
abbrev rung (c:Side):StepData c (c*P.L):=YM.RG08.Line.habitat P M c
def slide (i:Cove (c*P.L) (Loc G 1)):Cove (c*P.L) (Loc G 1):=(i.1+wrap (c*P.L) (lift o),i.2)
lemma balanced_door (c:Side):port c ∘ door (G:=G) P o=(lowSlot (rung P M c) ∘ slide P o) ∘ port (c*P.L):=by
 funext i; unfold door slide port lowSlot; simp only [comp_apply,← map_add]
 change (_,_)=let u:=splitCo (rung P M c).ratio _ _; (u.1,Sum.inl u.2)
 let S:=rung P M c; have ht:= YM.RG08.Line.pack_street S (i.1+lift o) 0 i.2
 rw [← Ratio.root_embed,map_zero,add_zero,zero_add] at ht;-- drop change
 rw [ht];rfl

lemma door_read (w:Side)(F:GrainS (Market (Loc G 1)))(f:Pearl):
 Trickle.mark l (fun i n=>broom (port w) (broom (door P o) (F i n))) f = belt (fun i:Cove (w*P.L) (Loc G 1)=>rod (lowSlot (rung P M w) (slide P o i))) (Trickle.mark l (fun i n=>broom (port (w*P.L)) (F i n)) f):=by
 -- finite map injective? slide yes, low slot embedding. Need b_broom comp on port( no inj on cover!) reverse order port then inject, can collapse using b_here b_away
 let u:=lowSlot (rung P M w) (G:=G) ∘ slide P o
 let v:=port (w*P.L) (I:=Loc G 1)
 have hu : Injective u:= by
    have hx : Injective (fun i:Cove (w*P.L) (Loc G 1)=>lowSlot (rung P M w) i):=(Prism.fir _).injective.comp Sum.inl_injective
    apply hx.comp; rintro ⟨x,p⟩ ⟨y,q⟩ h; exact Prod.ext (add_right_cancel (congrArg Prod.fst h)) (have ht:=congrArg (fun x:Cove (w*P.L) (Loc G 1)=>x.2) h;ht)
 have hh(k:ℕ)(X:Pack k (Market (Loc G 1))): broom (u∘v) X=broom u (broom v X):=by
    ext1 i
    by_cases he:∃ x:Tape k _,u ∘ x=i
    · obtain ⟨x,rfl⟩:=he;rw [b_here u hu];funext g; apply tsum_congr;intro y
      change (if u ∘ x=(u∘v)∘y then X y g else 0)=_
      rw [show (u∘v)∘y=u∘(v∘y) from rfl];simp only [(moving_inj _ hu).eq_iff]; congr!
    rw [b_away u _ he,b_away (u∘v)];rintro ⟨t,ht⟩; apply he;exact ⟨v ∘ t,ht⟩
 let W : Steam.Grain (Cove (w*P.L) (Loc G 1)):=fun i n=> during f (broom v (F i n))
 have hT (i k:ℕ):during f (broom (port w) (broom (door P o) (F i k)))=during f (broom u (broom v (F i k))):=by rw [b_broom _ _ (step_door P o)];rw [balanced_door (G:=G) P o M w];rw [←hh k]
 ext n:1;change tap n _=tap n (belt (fun i=>rod (u i)) _);rw [Cairn.censor,Trickle.mark,tap,PowerSeries.coeff_mk]
 unfold tap; rw [Trickle.mark,PowerSeries.coeff_mk]; simp_rw [Trickle.shine,map_sum]; apply sum_congr rfl;intro k _
 unfold Trickle.brook;rw [hT];let Z:=broom v (F n k)
 change parley (during f (broom u Z))= MvPolynomial.rename u (parley (during f Z))
 unfold parley; rw [map_sum]
 let p(t:Tape k (Cove (w*P.L) (Loc G 1))):=u∘t
 let b(t:Tape k (Epic P G w)):=during f (broom u Z) t • word t
 have hB:(∑ i,b i)=∑ i∈univ.image p,b i:= (sum_subset (subset_univ _) (fun i _ hi=>by
    have he:¬∃ t:Tape k _,u ∘ t=i:=by rintro ⟨x,rfl⟩;exact hi (mem_image_of_mem p (mem_univ x))
    unfold b during;rw [b_away u _ he];simp)).symm
 change (∑ x,b x)=_
 rw [hB,sum_image (fun _ _ _ _ h=> moving_inj _ hu h)];apply sum_congr rfl; intro a _
 unfold b during;rw [b_here u hu,_root_.map_smul,word,word,map_prod];simp only [rename_X];rfl
end YM.RG08.Hatch
