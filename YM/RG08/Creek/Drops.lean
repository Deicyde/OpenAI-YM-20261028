import YM.RG08.Creek.Signs
/-! # Start calc singleton sources. EXACT preimage laws on all budgets and stencil, and authorization. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I:Type} [Fintype I][DecidableEq I]{G:Gauge}{R v A B:ℝ}{L:Side}{T:Finset I}{k:I→ℕ}{e r τ D:ℕ}
-- Poise for one index is canonically Sight. Show synthesis is isometric. no R> due to product unit only, empty collapses.
private lemma spoke_eye (a:I)(b:I→Sight D R)(x:Zelt I D R): (speak ({a}:Finset I) b).val x=(b a).val (x a).1 (x a).2:= by
    change (∏ i:({a}:Finset I), (b i.val).val (x i.val).1 (x i.val).2) = _; rw [show (∏ i:({a}:Finset I), (b i.val).val (x i.val).1 (x i.val).2)=∏ i∈({a}: Finset I), (b i).val (x i).1 (x i).2 from Finset.prod_coe_sort _ (fun i=>(b i).val (x i).1 (x i).2), prod_singleton]
-- pack Sight→Scouts
private def mainZ (a:I)(D:ℕ)(R:ℝ): Sight D R→ₗ[ℝ] Scouts ({a}: Finset I) D R where
   toFun x:= speak ({a}: Finset I) fun _=>x
   map_add' u v:= (Scouts.tie _ D R).injective (Subtype.ext (ContinuousMap.ext fun x=> (spoke_eye a _ x).trans (by change (u.val _ _)+(v.val _ _)=Scouts.val (speak {a} (fun _=>u)) x + Scouts.val (speak {a} (fun _=>v)) x; rw [spoke_eye a,spoke_eye a])))
   map_smul' s u:= (Scouts.tie _ D R).injective (Subtype.ext (ContinuousMap.ext fun x=> (spoke_eye a _ x).trans (by change s*u.val _ _= s*Scouts.val (speak {a} (fun _=>u)) x; rw [spoke_eye a])))
private lemma mn (a:I)(b:I→Sight D R): mainZ a D R (b a)=speak {a} b:= spoke_eq D (fun i hi=> congr_arg b (mem_singleton.mp hi).symm)
private lemma emptyZ (a:I)(D:ℕ)(R:ℝ): Surjective (mainZ a D R) := by
   let U:=mainZ a D R
   rintro p; obtain ⟨⟨x,hx⟩,rfl⟩:=(Scouts.tie {a} D R).symm.surjective p
   induction hx using Submodule.span_induction with
   | mem x hp=> obtain ⟨i,rfl⟩:=hp; exact ⟨_,mn a i⟩
   | zero=> exact ⟨0,map_zero U⟩
   | add x y hx hq ih ih'=> obtain ⟨x',hx'⟩:=ih; obtain ⟨y',hy'⟩:=ih'; exact ⟨x'+y', (map_add U ..).trans (congr_arg₂ (· + ·) hx' hy')⟩
   | smul s x h ih=> obtain ⟨x,hx⟩:=ih; exact ⟨s • x,(map_smul U s x).trans (congr_arg (s • ·) hx)⟩
private def echoZ (a:I)(D:ℕ)(R:ℝ): Sight D R →ₗᵢ[ℝ] Scouts ({a}:Finset I) D R:= {
   (mainZ a D R) with
   norm_map' x:= by
      let v:=mainZ a D R x
      refine le_antisymm ((ContinuousMap.norm_le v.val (norm_nonneg x)).mpr (fun i=>?_)) ?_
      · rw [show v.val i=x.val _ _ from spoke_eye a (fun _=>x) i]; exact norm_mark D R _ _ x
      obtain ⟨b,rfl⟩:= doors D R x
      refine (bound D R _ (norm_nonneg v)).mpr fun i p=> ?_
      have hp : v.val (fun _=> (i,p))=mark D R b i p:= spoke_eye a (fun _=>sheet D R b) (fun _=> (i,p)); rw [← hp]; exact ContinuousMap.norm_coe_le_norm v.val _ }
private def freeZ (a:I)(D:ℕ)(R:ℝ): Sight D R≃ₗᵢ[ℝ] Scouts ({a}:Finset I) D R:= LinearIsometryEquiv.ofSurjective (echoZ a D R) (emptyZ a D R)
private def vend (a:I)(D:ℕ)(R:ℝ): Voice D R→ₗ[ℝ] Poise ({a}:Finset I) D R where
    toFun x:= x.comp (freeZ a D R).symm.toContinuousLinearEquiv.toContinuousLinearMap
    map_add' p q:= ContinuousLinearMap.ext fun _=>rfl
    map_smul' c p:= ContinuousLinearMap.ext fun _=>rfl
private lemma vend_c (a:I)(D:ℕ)(R:ℝ)(V:Voice D R): ‖vend a D R V‖ ≤ 1 * ‖V‖:= by
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x=>?_ ; let y:= (freeZ a D R).symm
    calc ‖V (y x)‖ ≤ ‖V‖*‖y x‖:= V.le_opNorm _
         _= _:= by rw [LinearIsometryEquiv.norm_map]

def questZ (a:I)(D:ℕ)(R:ℝ): Voice D R→L[ℝ] Poise ({a}:Finset I) D R:= (vend a D R).mkContinuous _ (vend_c a D R)
lemma quest_v (a:I)(D:ℕ)(R:ℝ): ‖questZ a D R‖≤1:= LinearMap.mkContinuous_norm_le _ zero_le_one _
lemma quest_eye (a:I)(b:I→Sight D R)(W:Voice D R): sampleK {a} b (questZ a D R W)= W (b a):= congr_arg W ((freeZ a D R).symm_apply_eq.mpr (mn a b|>.symm))

def markEye (U:I→BoardU D R G)(x: Places I)(a:I) : Screed (Poise ({a}:Finset I) D R) (Loc G 1):= fun i j=> roam (x a) (questZ a D R ∘ U a i j)
def markZ (U:I→BoardU D R G) : Layouts I G D R := fun x t=> if h:t.card=1 then let a:=(Finset.card_eq_one.mp h).choose; let hp:t={a}:=(Finset.card_eq_one.mp h).choose_spec; hp.symm ▸ markEye U x a else 0
variable {U:I→BoardU D R G}
lemma eye (p:Places I)(i:I): markZ U p {i}=markEye U p i:= by
   unfold markZ; split; next hv=>
     have hp: (card_eq_one.mp hv).choose=i:= (singleton_inj.mp (card_eq_one.mp hv).choose_spec).symm
     have hh(x y:I)(hv:x=y) : (congr_arg (fun a:I=>({a}:Finset I)) hv) ▸ markEye U p x = markEye U p y:= by subst y; rfl
     exact hh _ i hp
   simp_all
lemma eye_sh (p:Places I)(x:I→Sight D R)(i:I)(f: Exam D)(hf: x i=sheet D R f): access x (markZ U p) {i}=Town.season (p i) (ringU f (U i)):= by
   funext j k b; unfold access; rw [eye]; unfold markEye ringU Town.season roam
   simp only [Function.comp_apply]; rw [quest_eye, hf]; rfl
lemma eye_z (U:I→BoardU D R G)(p:Places I): markZ U p ∅=0:= dif_neg (by simp)
lemma style_empty :Styled τ (0:Screed (Poise T D R) (Loc G 1)):= ⟨fun i j=>Tidy.zero ..,cap_none⟩
lemma eyeSense (h:∀ i,Marvel (k i) (U i)): Sense k (markZ U):= by
   refine ⟨fun p T=> ?_,fun p x T=>?_,eye_z U,fun T=>?_⟩
   · by_cases H:T.card=1
     · obtain ⟨i,rfl⟩:=card_eq_one.mp H; rw [eye]; simp only [vanes,sum_singleton]; refine ⟨fun j v=> tidy_roam (Tidy.map _ ((h i).hem ..)) _,fun j k hv=> (h i).cap j k fun hz=>hv (funext fun b=>?_)⟩; simp [markEye,roam,hz]
     rw [markZ,dif_neg H]; exact style_empty
   · by_cases H:T.card=1
     · obtain ⟨i,rfl⟩:=card_eq_one.mp H; obtain ⟨v,hv⟩:= doors D R (x i); rw [eye_sh p x i v hv.symm, vanes,sum_singleton]; exact (Stone.graph (h i) _).transport _
     unfold access; rw [markZ,dif_neg H,show (fun i j=>sampleK T x ∘ (0:Screed (Poise T D R) (Loc G 1)) i j)=0 from funext fun i=>funext fun j=>funext fun z=>_root_.map_zero _]; exact Stone.zero
   intro x y H; by_cases h:T.card=1
   · obtain ⟨i,rfl⟩:=card_eq_one.mp h; dsimp only; rw [eye,eye]; unfold markEye; rw [H i (mem_singleton_self _)]
   simp only [markZ,h,↓reduceDIte]

lemma eyes_offer (a:I)(h:Quire.Lit (U a e r) v A) : Owns v ({a}: Finset I) (fun x=>markZ U x {a} e r) A:= by
   simp_rw [eye]; refine ⟨fun x y hp=>?_, Ink.nonneg h,fun i=> ⟨(fun _=>A),fun p=>?_,fun z=>?_⟩⟩
   · dsimp only; unfold markEye; rw [hp _ (mem_singleton_self _)]
   · have hv : loose {a} p a=p i:= by obtain ⟨b,h⟩:=i; obtain rfl:= mem_singleton.mp h; exact dif_pos h
     dsimp only; unfold markEye; rw [hv]
     exact bowed_ar _ (Ink.raise (Ink.some h _ (fun i=> (ling_pos _ _).le)) (mul_le_of_le_one_left (Ink.nonneg h) (quest_v a D R))) _
   let H:=Fleet ({a}: Finset I); let W:H:= fun _=>z; let K:= Held i z; let p:K:= ⟨W,rfl⟩; -- K subsingleton
   have hp(i':K): i'=p:= Subtype.ext (funext fun j=>by rw [Subsingleton.elim j i]; exact i'.property)
   let D':K→ℝ:= fun i=> if i=p then A else 0
   rw [show (fun (b:Held i z)=> Tribe i b.val v A)=D' from funext fun x=>?_]
   · exact ⟨fun i=> (if_pos (hp i) : D' i=A).ge.trans' (Ink.nonneg h),summable_of_ne_finset_zero (s:={p}) (fun i hi=>if_neg (mt mem_singleton.mpr hi)), le_of_eq ((tsum_eq_single p fun a h=>if_neg h).trans (if_pos rfl))⟩
   rw [show D' x=A from if_pos (hp x),hp x]; simp [Tribe,p,W,Mounts,size]
end YM.RG08.Creek
