import YM.TraceExtension.Perfect.Fossa
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {P:Patch}{Z:KernelChoices}{p:Clip}{G:Gauge}{μ A α B D H ι η σ C:ℝ} {V:Type}{F:Filter V}{n:ℕ}
-- receipt from planner
local notation "l!"=> (P.L.val:ℝ)
local notation "T"=> Slide G P Z p μ A α B
def SummitA (P:Patch) (G:Gauge)(Z:KernelChoices)(p:Clip)(μ A α B ι H:ℝ) := ∀ (X:Slide G P Z p μ A α B) (x:Site X.c)(o:Site X.f),8*(P.L.val+1)+4 ≤ X.f.val→separation (X.s.ratio.embed x) o ≤ 140*P.L.val→ ∀ a:ℝ,0≤a→a≤ι→ Settle (landW x) (landW o) (fun j z=>fderiv ℝ (X.salon o) 0 (desk z) j) (amber X.s X.k o) (aquifer X.s X.k o) a 4 (P.L.val:ℝ) H
lemma early_to (G:Gauge)(μ A α B:ℝ)(ι:ℝ)(h0:0<ι)(h0':ι<α)(hB:0≤B)(j:ℕ):∃ H:ℝ, 0 ≤ H∧ ∀ P:Patch,P.J=j→ ∀ Z p,SummitA P G Z p μ A α B ι H:=by
 obtain ⟨H,x,H'⟩:= Slide.early G μ A α B ι h0 h0' hB j 4 140 (by norm_num)
 exact ⟨H,x,fun P hp Z p V i v hx h=>H' P Z p V hp hx v i (by exact_mod_cast h)⟩

def SummitB (P:Patch)(G:Gauge)(Z:KernelChoices)(p:Clip)(μ A α B η D:ℝ):= ∀ (X:Slide G P Z p μ A α B) (x:Site X.c) (o:Site X.f), separation (X.s.ratio.embed x) o ≤ 140*P.L.val → ∀ v:ℝ, 0≤v→ v≤η→∀ k≤4,∀ j,sail (X.salon o) 0 (landW x) k j v 4 ((↑(landW o j):ℝ)/(P.L.val:ℝ)) ≤ D
lemma post_to (G:Gauge) (P:Patch)(Z:KernelChoices)(p:Clip)(μ A α B:ℝ)(hz:0<α):∃ η D:ℝ,0<η∧ 0≤ D∧ SummitB P G Z p μ A α B η D:=by
 obtain ⟨a,D,h,hD,H⟩:= Slide.early_uniform G P Z p μ A α B 140 (by norm_num) hz 4 4
 exact ⟨a,D,h,hD,fun X x o hh v hv ht k h j=>H X o x (by exact_mod_cast hh) k j h v hv ht⟩

-- report-sourced transfer germ
local notation "RAY" => (fun n : Side=> Acr G n→ℝ)
variable (X : V→ Slide G P Z p μ A α B)
structure LotFee (F:Filter V)(X:V→ Slide G P Z p μ A α B)(u v H D:ℝ) : Prop where
 quiet : Tendsto (fun w=>(X w).c.val) F atTop
 large : ∀ᶠ w in F, max (8*(P.L.val+1)+4) 11 ≤ (X w).f.val
 S : SummitA P G Z p μ A α B u H
 T' : SummitB P G Z p μ A α B u D
 sum : 0<u∧0<v ∧ u/(P.L.val:ℝ) ≤ v ∧ 0<α∧0 ≤ B ∧ 0≤ H∧0≤D
structure Tour (X:V→ Slide G P Z p μ A α B) (J:∀ w,Site (X w).f → Acr G (X w).f→ℝ)(K:∀ w,Site (X w).f→Acr G (X w).c→ℝ): Prop where
 J'(w)(x:Site (X w).f): ContDiffAt ℝ ω (J w x) 0
 W'(w)(x:Site (X w).f): fderiv ℝ (J w x) 0=0
 law(w)(x:Site (X w).f): K w x=ᶠ[𝓝 0] J w x ∘ (X w).salon x
 rise(w)(x:Site (X w).f): K w x=ᶠ[𝓝 0] J w x ∘ (X w).dig
namespace Tour
variable {X}{J:∀ w,Site (X w).f → Acr G (X w).f→ℝ}{K:∀ w,Site (X w).f→Acr G (X w).c→ℝ}
lemma plus {J' K'} (H:Tour X J K)(h :Tour X J' K'): Tour X (fun w z=>J w z+J' w z) (fun w z=>K w z+K' w z):=by
 refine ⟨fun w x=> (H.J' w x).add (h.J' w x),fun w x=>?_,fun w x=>(H.law w x).add (h.law w x),fun w x=>(H.rise w x).add (h.rise w x)⟩
 rw [fderiv_add (H.J' w x|>.differentiableAt (by simp)) (h.J' w x|>.differentiableAt (by simp)),H.W',h.W',add_zero]
lemma away {J' K'} (H:Tour X J K)(h :Tour X J' K'): Tour X (fun w z=>J w z-J' w z) (fun w z=>K w z-K' w z):=by
 refine ⟨fun w x=> (H.J' w x).sub (h.J' w x),fun w x=>?_,fun w x=>(H.law w x).sub (h.law w x),fun w x=>(H.rise w x).sub (h.rise w x)⟩
 rw [fderiv_sub (H.J' w x|>.differentiableAt (by simp)) (h.J' w x|>.differentiableAt (by simp)),H.W',h.W',sub_zero]
end Tour
variable {u v:ℝ}{X}{J:∀ w,Site (X w).f → Acr G (X w).f→ℝ}{K:∀ w,Site (X w).f→Acr G (X w).c→ℝ}
variable (s : LotFee F X u v H D)(ℓ:Tour X J K) (x:∀ w,Site (X w).c)(q:Cover)
set_option quotPrecheck false
local notation "x!"=> fun w=> (X w).s.ratio.embed (x w)+wrap (X w).f q
include s ℓ
lemma Tour.be (h: 0 ≤ C)(p:ℕ)(U : Tit G→Tit G→ℝ)(hU: ∀ i j, ScoreG i+ScoreG j<p→ U i j=0)
   (hp: Ear F (x!) (fun w=>J w (x! w)) v 2 C)(ht:Tip F (x!) (fun w=>J w (x! w)) U p):
     Tip F x (fun w=>K w (x! w)) (((↑(P.L.val):ℝ))⁻¹ ^ p • U) p:=by
 obtain ⟨ha,hv,hy,hz,hB,hx⟩:=s.sum
 have he:= Slide.smooth_cost X x q hU ht.sees hp.h (fun i=>ℓ.W' ..) s.quiet hz hB 4 le_rfl hv (show 0 ≤ C+1 by linarith) (hp.fee _ zero_lt_one)
 exact (Tip.mk (f:=fun w=> J w (x! w) ∘ (X w).dig) (fun w=> ContDiffAt.comp _ ((X w).dig_zero.symm ▸ hp.h w) (X w).dig_pay) (show Stoke F x _ (_ • U) p from he)).likewise (fun w=> (ℓ.rise ..).symm)
variable (hq: size q ≤ 140*P.L.val)
include hq
omit ℓ in
private lemma toll (w:V): separation ((X w).s.ratio.embed (x w)) (x! w) ≤ 140*P.L.val:=by let y:=(X w).s.ratio.embed (x w); change separation y (y+_) ≤ _; rw [separation_comm,separation, add_comm y,add_sub_cancel_right]; exact (Next.Free.within_size ..).trans hq
set_option quotPrecheck false
local notation "K_"=> fun w=>(X w).s
local notation "P_"=> fun w=>(X w).k
local notation "J!"=> fun w=> J w (x! w)
local notation "W_"=> fun w=> (X w).salon (x! w)
omit ℓ in
private lemma spurt : ∀ᶠ w in F, Settle (landW (x w)) (landW (x! w)) (fun a b=> fderiv ℝ (W_ w) 0 (desk b) a) (amber (K_ w) (P_ w) (x! w)) (aquifer (K_ w) (P_ w) (x! w)) u 4 (P.L.val:ℝ) H:=by
 refine s.large.mono (fun w hv=> s.S (X w) _ _ ((le_max_left ..).trans hv) (toll s x q hq w) u s.sum.1.le le_rfl)
lemma Tour.boon (i:ℕ)(he:2 ≤ i)(hv:i ≤ 4)(C:ℕ→ℝ)(hC:∀ i,0 ≤ C i)(hk:∀ k,k ≤ i→2≤ k→Ear F (x!) (fun w=> J w (x! w)) v k (C k)): Ear F x (fun w=> K w (x! w)) u i
     (((2*H/(P.L.val:ℝ)^2)^i*C i) + ∑ z∈ univ.erase (OrderedFinpartition.atomic i), D^z.length*C z.length):=by
 obtain ⟨ha,hb,h,hp,hx,hHH,D'⟩:=s.sum
 have hf:= billed_all K_ P_ W_ (x!) x P.L (J!) (fun w=>ℓ.J' ..) (fun w=> (X w).salon_pay _) (fun w=>(X w).salon_zero _) (fun w=>ℓ.W' ..) hHH (spurt s x q hq) D' ha.le hv he h (Eventually.of_forall (fun w j k hh=>s.T' (X w) _ _ (toll s x q hq w) _ ha.le le_rfl _ (hh.trans hv) _)) C hC (fun i ip ih=> (hk i ip ih).fee)
 rw [mul_comm H 2] at hf; apply Ear.likewise (Ear.mk (f:=fun w=> J! w ∘ W_ w) (fun w=>ContDiffAt.comp _ (by dsimp only; rw[Slide.salon_zero]; exact ℓ.J' ..) ((X w).salon_pay _)) hf); exact fun w=>(ℓ.law w _).symm
lemma Tour.bear (hp:Ear F (x!) (fun w=>J w (x! w)) v 2 C) (ht:Tip F (x!) (fun w=>J w (x! w)) 0 4):
    Ear F x (fun w=>K w (x! w)) u 2 (((2:ℝ)^13 * H^2/(P.L.val:ℝ)^5)*C):=by
 obtain ⟨ha,hb,h,hp',hx,hH,hD⟩:=s.sum
 have hh:= billed_near K_ P_ W_ (x!) x P.L (J!) (fun w=>ℓ.J' ..) (fun w=>(X w).salon_pay _) (fun w=>(X w).salon_zero _) (fun w=>ℓ.W' ..) hH (spurt s x q hq) ht.sees ha.le le_rfl (s.large.mono fun w hv=>(le_max_right ..).trans hv) h _ hp.fee
 apply Ear.likewise (Ear.mk (f:=fun w=> J! w ∘ W_ w) (fun w=>ContDiffAt.comp _ (by dsimp only; rw[Slide.salon_zero]; exact ℓ.J' ..) ((X w).salon_pay _)) hh); exact fun w=>(ℓ.law w _).symm
lemma Tour.boar (hp: Ear F (x!) (fun w=> J w (x! w)) v 2 C)(ht:Tip F (x!) (fun w=> J w (x! w)) 0 5): Ear F x (fun w=>K w (x! w)) u 2 (((2:ℝ)^12* H^2/(P.L.val:ℝ)^6)*C):=by
 obtain ⟨ha,hb,h,hp',hx,hH,hD⟩:=s.sum
 have hh:= billed_after K_ P_ W_ (x!) x P.L (J!) (fun w=>ℓ.J' ..) (fun w=>(X w).salon_pay _) (fun w=>(X w).salon_zero _) (fun w=>ℓ.W' ..) hH (spurt s x q hq) ht.sees ha.le le_rfl (s.large.mono fun w hv=>(le_max_right ..).trans hv) h _ hp.fee
 apply Ear.likewise (Ear.mk (f:=fun w=> J! w ∘ W_ w) (fun w=> ContDiffAt.comp _ (by dsimp only; rw[Slide.salon_zero]; exact ℓ.J' ..) ((X w).salon_pay _)) hh); exact fun w=>(ℓ.law w _).symm
end YM.Trace.Perfect
