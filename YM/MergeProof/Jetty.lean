import YM.MergeProof.Pitch
import YM.MergeProof.SwitchCost


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Merge.Switch Merge
variable [Fintype I] {w:V→ℝ} {F:Y→Ways I} {d t:ℝ} {z:I→Poly B}
lemma crystal (h:Switch.Paid F d) (he:∀ i,0<w i) (hz:∀ i,Poly.price w (z i) ≤ 1): Loci w (fun U=>sound z (F U)) d:=by
   obtain ⟨p,hp,h,H⟩:=h
   let f (x:Finset I):=∏ i∈x,z i; have hf(x): Poly.price w (f x)≤1:= (Poly.multiple he x z).trans (Finset.prod_le_one (fun i _=> Poly.nonnegative he (z i)) (fun i _=> hz i))
   let g(i:B.Mode)(x:Finset I):= p x * ‖(f x).part i‖
   refine ⟨fun i=>∑ x,g i x,fun i=>sum_nonneg fun x _=> mul_nonneg (hp _) (norm_nonneg _),fun y i=>?_,?_⟩
   · obtain ⟨G,hG,hZ⟩:=H y; dsimp only; rw [Switch.sound,hG.exact,mapScores_apply,Poly.part_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun x _=> ?_); rw [Poly.part_smul,norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_right (hZ 0 ⟨le_rfl,zero_le_one⟩ x) (norm_nonneg _) -- p
   unfold wordsPrice g; simp_rw [Finset.mul_sum,mul_left_comm (Poly.toll ..) (p _)]; rw [sum_comm]; exact (Finset.sum_le_sum (g:=p) fun i _=> by rw [← mul_sum]; exact mul_le_of_le_one_right (hp i) (hf i)).trans h

variable {P:Support n}{o:V→Site n}{u:Config G n→Ways I}
local notation "g0"=> fun U=> sound z (u U)
lemma bear [Fintype V] (ht:∀ p:Finset I,let f U:=jet (u U) p; UsesFinal t P f ∧ GaugeInvariant f∧ Measurable f∧∀ U,f U≠0→∀ i∈p,GridApprox.Nil.Scoped (A:={i| o i∈P}) (z i)): Borne o P (fun U=>sound z (u U)) t:=by
   refine ⟨fun U V h hV=>congr_arg (mapScores B z) (funext fun i=>(ht i).1 U V h hV),fun g U=> congr_arg (mapScores B z) (funext fun i=>(ht i).2.1 g U),fun i=>?_,fun U i hi=>?_⟩
   · simp_rw [sound,mapScores_apply,Poly.part_sum,Poly.part_smul]; exact Finset.measurable_fun_sum _ fun p _=> (Complex.continuous_ofReal.measurable.comp (ht p).2.2.1).mul measurable_const
   rw [sound,mapScores_apply,Poly.part_sum]; refine Finset.sum_eq_zero (fun j _=> ?_); rw [Poly.part_smul]; by_cases hp:jet (u U) j=0; rw [hp,Complex.ofReal_zero,zero_mul]; rw [scope_prod _ _ ((ht j).2.2.2 U hp) i hi,mul_zero]
lemma freight {T : Prop} (U:Config G n) (h:∀ p:Finset I,jet (u U) p≠0→T) (hu:sound z (u U)≠0): T:=by
   by_contra hn; apply hu; rw [sound,show jet (u U)=0 from funext fun i=> not_not.mp (mt (h i) hn),map_zero]
lemma quality (F: Y→Ways I)(z:I→Poly B)(U:Y)(p:V)(hv:∀ i,(z i).part B.quiet=0) : (sound z (F U)).part (B.fire p)=∑ i,(jet (F U) {i}:ℂ)*(z i).part (B.fire p):=by
   unfold sound; rw [mapScores_apply,Poly.part_sum]; let f(i:Finset I):= (jet (F U) i:ℂ)*(∏ j∈i,z j).part (B.fire p)
   simp_rw [Poly.part_smul]; change ∑ i,f i= _; rw [← show ∑ i∈ (Finset.univ.image fun i:I=>({i}:Finset _)),f i=∑ i,f i from ?_,sum_image]; exact Finset.sum_congr rfl (fun i _=>congr_arg (_ * ·) (by rw [Finset.prod_singleton]))
   · intro i _ j _ he; exact Finset.singleton_inj.mp he
   refine Finset.sum_subset (subset_univ _) (fun i _ h=>?_); unfold f; rw [shockProd, sum_eq_zero, mul_zero]; intro j hj
   have hp: (i.erase j).Nonempty:= Finset.nonempty_iff_ne_empty.mpr (fun hh=> h (Finset.mem_image.mpr ⟨j,Finset.mem_univ _, show {j}=i from by rw [show i= {j} from ?_]; have ha:= Finset.insert_erase hj; rwa [hh,Finset.insert_empty,eq_comm] at ha⟩))
   obtain ⟨l,hl⟩:=hp; rw [prod_eq_zero hl (hv l),mul_zero]
end YM.MergeProof.Accent
