import YM.TraceExtension.Perfect.Gist
import YM.TraceExtension.Perfect.Riff
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α C D s B Λ:ℝ}
variable {F:Forest S.ratio}{ρ:Bid.Dir G c→AxisChart G F} (t:S.Choices)
abbrev Peat (G:Gauge)(c:Side):= Config G c→ℝ
abbrev Gal (G:Gauge)(c:Side):=Config G c→Link G c

def aroma (p:Clip)(M:PathData G)(Y:Gal G f)(V:Config G f):= fderiv ℝ (burn p M V) 0 (Y V)
abbrev sniff (M:PathData G)(p:Clip): Gal G f→ₗ[ℝ] Peat G f:={
 toFun:=aroma p M
 map_add':=fun X Y=>funext fun v=> map_add _ _ _
 map_smul':=fun c X=>funext fun v=> (fderiv ℝ (burn p M v) 0).map_smul c (X v) }
private lemma burn_roll (p:Clip)(M:PathData G)(k:Coats G f)(V:Config G f)(hp:M.Bounds p η C D)(u:Link G f) : fderiv ℝ (burn p M (Lattice.gauge k V)) 0 (armor k u) = fderiv ℝ (burn p M V) 0 u:=by
 let W:= Lattice.gauge k V
 have hD: ContDiffAt ℝ ω (burn p M W) 0:= Work.F02.mainTerm_contDiffAt (A:=fun y:Link G f=>input G f y*W) hp ((Army.powL (v:=id) contDiffAt_id).mul (Army.park W _))
 rw [← burn_carry k hp V, fderiv_comp 0 _ (armor k).differentiableAt, map_zero]
 · rw [(armor k).fderiv]; rfl
 rw [map_zero]; exact hD.differentiableAt (by simp)
lemma aroma_diff {Y:Gal G f}(hp: M.Bounds p η C D)(hY:Cloaked Y): Cleric (aroma p M Y) :=by
 let Z x:=fderiv ℝ (burn p M (input G f x)) 0
 have hz: ContDiffAt ℝ ω Z 0:=by
    have hw: ContDiffAt ℝ ω (uncurry (fun x=>burn p M (input G f x))) 0:=by
       let T:= fun v:Link G f × Link G f=>input _ _ v.2*input G f v.1
       exact Work.F02.mainTerm_contDiffAt (A:=T) hp ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.powL contDiffAt_fst))
    exact (Work.F05.curve_partial hw).comp (f:=fun x: Link G f=>(x,0)) 0 (by fun_prop)
 refine ⟨hz.clm_apply hY.dye,?_⟩
 intro T _ _ _ _ V k a hV hv hk h
 filter_upwards [hY.jacket T V k a hV hv hk h] with x hx
 change aroma _ _ _ _=aroma _ _ _ _
 unfold aroma; rw [show Y (Lattice.gauge (k x) (V x))=_ from hx]
 exact burn_roll _ _ _ _ hp _
lemma aroma_transfer (h:S.patch.Branches S.kernel G)(h':Critical F p M ρ)(hp:M.Bounds p η C D)(he:ClassicalMatch F p u M R ρ)(hk:R.Bounds u s B Λ){Y:Gal G f}(hY:Cloaked Y)(hy:Y 1=0): braid (inheritJ F ρ (aroma p M Y) ∘ input G c) (aroma u R (inheritY F ρ t Y) ∘ input G c) 0 4:=by
 let A:=encamp F ρ; let X:=fun x=> Y (A x).1
 have he': A 0=1:= encamp_zero h'; have hv : X 0=0:=by dsimp only [X]; rw [he']; exact hy
 have hX: ContDiffAt ℝ ω X 0:= hY.put _ ((camp_thaw h').1) (congr_arg Prod.fst he')
 apply (braided inspire).trans; refine (recoup ρ t h h' hp he hX hv).trans (braided ?_)
 filter_upwards [inmate (Y:=Y) t] with x hx; unfold X
 change _= aroma _ _ _ _; rw [aroma, show inheritY _ _ _ _ (input _ _ x)=_ from hx]
 let U:=input G c x
 have hU:ContDiffAt ℝ ω (burn u R U) 0 := Work.F02.mainTerm_contDiffAt (A:=fun v:Link G c=>input _ _ v*U) hk ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _))
 simp only[shuttle,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,cant_zero_slope (V:=input G c x) hk hU,add_zero]; rfl

-- induction generic
lemma Sheaf.mount {M:Type*}[AddCommGroup M][Module ℝ M] (P:Submodule ℝ M)(J:Cover→M)(S:Sheaf)(h:∀ x,J x∈P): ∀ a, S.take J a∈ P:=by
 induction S generalizing J with
 | stay=>intro a;rw [Sheaf.take]; exact P.zero_mem
 | mon=>intro a;rw [Sheaf.take]; exact h _
 | scale c X p=>intro a; rw [Sheaf.take]; exact P.smul_mem _ (p J h a)
 | duo X Y p v=>intro a;rw [Sheaf.take]; exact P.add_mem (p J h a) (v J h a)
 | mix X Y p v=>intro a; rw [Sheaf.take]; exact p _ (v J h) a
lemma Sheaf.inherit {M V:Type*}[AddCommGroup M][Module ℝ M][AddCommGroup V][Module ℝ V](F:M→ₗ[ℝ] V)(J:Cover→M)(S:Sheaf): F ∘ S.take J=S.take (F∘J):=by induction S generalizing J with
| stay=>ext1 x; simp [Sheaf.take]
| mon=>rw[Sheaf.take,Sheaf.take]; rfl
| scale c X p=>simp only[Sheaf.take,← p]; funext x; exact F.map_smul ..
| duo X Y p v=>simp only[Sheaf.take,← p,← v]; funext x; exact F.map_add ..
| mix X Y p v=> rw [Sheaf.take,Sheaf.take,p,v]
lemma verse_map {M V:Type*}[AddCommGroup M][Module ℝ M][AddCommGroup V][Module ℝ V](F:M→ₗ[ℝ] V)(J:Site f→M)(r:Ratio c f)(S:Sheaf): F ∘ verse S r J=verse S r (F∘J):=funext fun x=> congr_fun (Sheaf.inherit F (fun w=> J (r.embed x+wrap f w)) S) 0
lemma verse_mem {M:Type*} [AddCommGroup M][Module ℝ M](P:Submodule ℝ M)(J:Site f→M)(r:Ratio c f)(S:Sheaf)(h:∀ x,J x∈ P)(x:Site c): verse S r J x∈P:=Sheaf.mount P _ _ (fun q=>h (r.embed x+wrap f q)) 0

def clergy (G:Gauge)(f:Side): Submodule ℝ (Peat G f) where
 carrier:= setOf Cleric
 zero_mem':=⟨contDiffAt_const,fun _ _ _ _ _ _ _ _ _ _ _ _=>EventuallyEq.rfl⟩
 add_mem' := by
    intro a b ha hb; change Cleric a at ha; change Cleric b at hb
    refine ⟨ha.dye.add hb.dye, fun T _ _ _ _ V t u hV hv ht hh=>(ha.jacket T V t u hV hv ht hh).add (hb.jacket T V t u hV hv ht hh)⟩
 smul_mem':=by
    intro c a ha; change Cleric a at ha
    refine ⟨contDiffAt_const.smul (g:=a∘input G f) (f:=fun _=>c) ha.dye, fun T _ _ _ _ V t u hV hv ht hh=>?_⟩
    filter_upwards [ha.jacket T V t u hV hv ht hh] with x hx; exact congr_arg (fun f:ℝ=>c • f) hx

def rains (G:Gauge)(f:Side): Submodule ℝ (Gal G f) where
 carrier:= setOf fun Y=> Cloaked Y ∧ Y 1=0
 zero_mem':=⟨⟨contDiffAt_const, fun _ _ _ _ _ V t _ _ _ _ _=>Eventually.of_forall (fun x=> ((armor (t x)).map_zero).symm)⟩,rfl⟩
 add_mem':=by
   rintro a b ⟨h,h'⟩ ⟨p,p'⟩; refine ⟨⟨h.dye.add p.dye,fun T _ _ _ _ V t u hV hv ht hh=>?_⟩,by simp only [Pi.add_apply,h',p',add_zero]⟩
   filter_upwards [h.jacket T V t u hV hv ht hh,p.jacket T V t u hV hv ht hh] with x hX hY
   simp only [Pi.add_apply,map_add]; rw [hX,hY]
 smul_mem':=by
   rintro c a ⟨h,h'⟩; refine ⟨⟨contDiffAt_const.smul (g:=a ∘ input G f) (f:=fun _=>c) h.dye,fun T _ _ _ _ V t u hV hv ht hh=>?_⟩,by simp only[Pi.smul_apply,h',smul_zero]⟩
   filter_upwards [h.jacket T V t u hV hv ht hh] with x hx; simp only [Pi.smul_apply,map_smul]; rw [hx]

-- braid pairs module
local notation "Z"=> input G c
variable (G c) in
def wing: Submodule ℝ ((Peat G c) × (Peat G c)) where
 carrier:=setOf fun u=> Cleric u.1 ∧ Cleric u.2 ∧ braid (u.1 ∘ Z) (u.2 ∘ Z) 0 4
 zero_mem':= ⟨(clergy _ _).zero_mem,(clergy _ _).zero_mem,fun _ _=>rfl⟩
 add_mem':=by
    rintro ⟨u,v⟩ ⟨p,q⟩ ⟨hx,hf,h⟩ ⟨hy,hz,H⟩; refine ⟨(clergy _ _).add_mem (x:=u) hx (y:=p) hy,(clergy _ _).add_mem (x:=v) hf (y:=q) hz,fun i hi=>?_⟩
    change iteratedFDeriv ℝ i (u∘Z+p∘Z) 0=iteratedFDeriv ℝ i (v∘Z+q∘Z) 0
    rw [iteratedFDeriv_add_apply (hx.dye.of_le le_top) (hy.dye.of_le le_top),iteratedFDeriv_add_apply (hf.dye.of_le le_top) (hz.dye.of_le le_top),h _ hi,H _ hi]
 smul_mem':=by
    rintro s ⟨u,v⟩ ⟨hx,hf,h⟩; refine ⟨(clergy _ _).smul_mem (x:=u) s hx,(clergy _ _).smul_mem (x:=v) s hf,fun i hi=>?_⟩
    change iteratedFDeriv ℝ i (s • (u ∘ Z)) 0=iteratedFDeriv ℝ i (s • (v∘Z)) 0; rw [iteratedFDeriv_const_smul_apply, iteratedFDeriv_const_smul_apply, h _ hi]
    exact hf.dye.of_le le_top
    exact hx.dye.of_le le_top
end YM.Trace.Perfect
