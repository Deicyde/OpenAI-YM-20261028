import YM.TraceExtension.Perfect.Trove
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{η C V σ D A Λ:ℝ}{R:PathData G}{B:Bed}
def bornT (a b:Axis)(x:Site f) := born (G:=G) x a b
def dust (p:Clip)(R:PathData G)(a:Axis)(x:Site f): Peat G f:= (∑ b:Axis,elm b (bornT b a) x) - aroma p R (mist x a)
def dawn (p:Clip)(R:PathData G)(f:Side): Dart G f where
 J:=bornT
 Y:=fun i x=> mist x i
 E:=dust p R
 Q:=0
 twist:=0

def coco (a b:Axis)(x:Site f): loom G f:= ⟨bornT a b x,born_home ..⟩
lemma elm_y (x:Site f)(a b:Axis): ((elm a (coco (G:=G) a b) x).val)=elm a (bornT a b) x:=by unfold elm Pull.dTap;simp only [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,Submodule.coe_sub];rfl
lemma ivy (h:R.Bounds p σ D Λ)(hp:Floor B p f η V)(he:Attached B R)(hv:Bid.Sworn B f G): Dart.Sound (dawn p R f) R p:=by
 refine ⟨fun a b x=>born_home ..,fun a x=>mist_home ..,fun a x=> ?_,fun a i=>(loom _ _).zero_mem,fun a b k i=>(loom _ _).zero_mem,?_, fun a b=>?_,fun b i=>?_⟩
 · apply (loom _ _).sub_mem _ ((aroma_gone h hp he hv ..).1); exact (loom _ _).sum_mem fun i _=>(elm_y x i a) ▸ (elm i (coco i a) x).property
 · ext1 x; simp only [dawn,bornT,Finset.sum_apply,twig,Pi.zero_apply,sub_self,born_trace,sum_const_zero]
 · ext1 x; simp only[dawn,bornT,Finset.sum_apply,twig,Pi.zero_apply,sub_self,Pi.sub_apply]; rw[born_symm x a b];simp
 simp only [dawn,dust,Pi.sub_apply,Finset.sum_apply, sub_sub_cancel]; refine ⟨aroma_diff h (mist_analytic _ _),aroma_diff h (mist_analytic _ _),fun i hi=>rfl⟩

-- period tastes for all offsets
variable {W:Type}{F:Filter W}{n:W→Side}(x:∀ w,Site (n w))(ht:Tendsto (fun w=>(n w).val) F atTop)
include ht
lemma fill_born (s t: Tit G)(a b:Axis)(v:Cover): ∀ᶠ w in F, loom₂ (n w) G (ballad s (x w)) (ballad t (x w)) (coco a b (x w+wrap (n w) v))=north s t v a b:=by
 filter_upwards [eventually_all.mpr (fun a=> eventually_all.mpr fun b=>stately x ht s v a b),eventually_all.mpr (fun a=> eventually_all.mpr fun b=>stately x ht t v a b)] with w hs hv
 let y:= x w+wrap (n w) v
 let U(i j k):loom G (n w):=⟨bornPair y i j k,(born_win ..).1⟩
 let K:= (∑ i:Axis,∑ j:Axis, U i i j)
 let Z:= ∑ k:Axis,U a b k
 have hh: coco (G:=G) a b y=(if a=b then (1/4:ℝ) • K else 0)-Z:=by
    ext1; simp only[Z,K,apply_ite Subtype.val,Submodule.coe_sub,AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul]; rfl
 let H:= loom₂ (n w) G (ballad s (x w)) (ballad t (x w))
 have hx(i j k): H (U i j k)=NB s t v i j k:=by
    unfold NB; simp_rw [← hs, ← hv]; change iteratedFDeriv ℝ 2 (ballX (bornPair y i j k)) 0 _=_; rw [loom_banks (U i j k |>.property),(born_win y i j k).2]; rfl
 change H (coco a b y)=_; rw [hh,map_sub]; unfold north K Z; split_ifs <;> simp only[map_smul,map_zero,map_sum,hx,smul_eq_mul]
lemma verdant (a b:Axis): Stoke F x (fun w=>ballX (born (x w) a b)) (fun s t=>north (G:=G) s t 0 a b) 4:=by
 refine ⟨fun s t h=> tendsto_const_nhds.congr' ?_⟩
 filter_upwards [fill_born x ht s t a b 0] with w he; rw [map_zero,add_zero] at he; exact he.symm
lemma varsity (a:Axis): Stoke F x (fun w=>bottom (mist (x w) a)) (missY (G:=G) a) 5 :=by
 refine ⟨fun s t h=>tendsto_const_nhds.congr' ?_⟩
 filter_upwards [eventually_all.mpr (fun i=>stately x ht s 0 a i), eventually_all.mpr (fun i=>stately x ht t 0 a i)] with w hp hv
 rw [(rain_read (mist_home (x w) a)).2.2.2, mist_slope, mist_slope, show ∀ t: Tit G,(bite G _ (ballad t (x w))).2=capGauge t (x w) from fun _=> rfl]
 change _= (petalPush (x w) a (bGauge s (x w))) ⬝ᵥ (capGauge t _)+(petalPush (x w) a (bGauge t _)) ⬝ᵥ (capGauge s _)
 rw [dot_watch,dot_watch]; simp only[map_zero,add_zero] at hp hv; simp_rw[hp,hv]; rfl
lemma yellow (a b:Axis)(s t:Tit G)(h:ScoreG s+ScoreG t≤5): ∀ᶠ w in F, loom₂ (n w) G (ballad s (x w)) (ballad t (x w)) (elm a (coco a b) (x w))=riseB s t a a b:=by
 filter_upwards [eventually_all.mpr (fun i:Fin 4=> fill_born x ht s t a b ((Pull.steps i :ℤ) • step a)), eventually_all.mpr (fun i:Fin 4=>fill_born x ht s t a b ((-(Pull.steps i:ℤ)) • step a))] with w hh h'
 unfold elm Pull.dTap; rw [map_sum]; simp only [map_sub,map_smul,zero_add, zero_sub,smul_eq_mul]
 simp_rw [map_zsmul, wrap_step, north_line s t h] at hh h'; simp_rw [hh,h']; push_cast
 have hp:= Pull.credit 1 (by decide); simp only[pow_one] at hp; let C:=riseB s t a a b
 have ht : (∑ i: Fin 4,Pull.cash i * (↑(Pull.steps i)-(-(↑(Pull.steps i):ℝ))))*C= C:= by rw[hp];simp
 rw[Finset.sum_mul] at ht; apply Eq.trans _ ht; apply sum_congr rfl; intro i _; unfold C; ring
end YM.Trace.Perfect
