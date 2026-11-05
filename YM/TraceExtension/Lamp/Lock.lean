import YM.TraceExtension.Lamp.Taps
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
abbrev Maze G f:= Link G f→ℝ
-- characteristic stake
variable (d i:Axis)(q:G.ColorIndex)
def mood (G:Gauge) (i:Axis)(x:G.ColorIndex):Loc G 1:=(coord i,x)
abbrev ra (d:Axis)(x:ℤ):Cover:= x • step d
abbrev reab (d b:Axis)(x:Dish) : Cover:= -ra d x.1 + ra b x.2
abbrev lawn (d b:Axis)(x:Dish):TresF (Fin 2):= flee (step d) (step b) x
lemma reeling (b:Axis) (x:Dish): lawn d b x= ![reel (ra d x.1),reel (reab d b x)]:=by funext i; unfold lawn flee reab ra; rw [reel_be,reel_neg,reel_z,reel_z,reel_i,reel_i]
abbrev clipP (F: Maze G f)(x y:Site f):ℂ:=beat F 0 2 ![relay x (mood G i q),relay y (mood G i q)]
def cue (b:Axis)(F: Maze G f)(x:Dish):=clipP i q F (wrap f (ra d x.1)) (wrap f (reab d b x))
def lux (b:Axis)(F: Maze G f):ℂ:=Deb fun x:Dish=> ((pitchf f:ℂ)⁻¹)^(3:ℕ)*cue d i q b F x
def pia (b:Axis)(F: Maze G f):ℂ:= Deb fun x:Dish=> neap 3 (molt (0:Site f) ![mood G i q,mood G i q] F) 0 (lawn d b x)
def cob (F: Maze G f):ℂ:= PanZ fun x:ℤ=> ((pitchf f:ℂ)⁻¹)^ (2:ℕ)*clipP i q F (wrap f (ra d x)) (-(wrap f (ra d x)))
lemma cue_at (b:Axis)(F:Maze G f)(x:Dish): cue d i q b F x=molt 0 ![mood G i q,mood G i q] F (pitchf f • lawn d b x):=by
    rw [molt_be]; unfold cue clipP; rw[reeling]
    congr 1
    ext1 k
    fin_cases k
    · ext1 j; change cell (wrap f (ra d x.1)) j.1 * _= mode (axes (pitchf f • reel (ra d x.1))) (lift (j.1-0))*_; rw[←(reel_roll ..).exp,sub_zero];rfl
    ext1 j; change cell (wrap f (reab d b x)) j.1 * _= mode (axes (pitchf f • reel (reab d b x))) (lift (j.1-0))* _; rw[←(reel_roll ..).exp,sub_zero];rfl
lemma clue_at (b:Axis)(F:Maze G f)(x:ℤ): clipP i q F (wrap f (ra d x)) (-(wrap f (ra d x)))=cue d i q b F (x,0):=by rw[cue,reab]; simp [ra]
section limit
variable (Q: Tendsto (fun w=>(g w).val) L atTop)
include Q
lemma gran : Wilt L (pitchf ∘ g):=by
    refine ⟨fun w=> pitch_pos,?_⟩
    let f(w:W):ℝ:=↑((g w).val); have hp:Tendsto f L atTop:=tendsto_natCast_atTop_atTop.comp Q
    exact tendsto_const_nhds.div_atTop hp
variable (F:∀ w,Maze G (g w))(h:Pico (fun _=>0) F 2)
include h
omit Q in
lemma joined : Honor (fun w=> molt (0:Site (g w)) (![mood G i q,mood G i q]) (F w)) n:=by
    obtain ⟨A,C,hA,hC,H⟩:=h.top;exact ⟨_,mul_nonneg (ramt_n (k:=n) (I:=Fin 2) hA) hC,fun _ _=> malt (H _) hA hC _ _ _⟩
lemma lux_neap (b:Axis): Rose L (fun w=>lux d i q b (F w)) (fun w=> pia d i q b (F w)):=by
    let A:TresF (Fin 2):= ![step d,-step d]; let X:TresF (Fin 2):= ![0,step b];
    let U w:= molt (0:Site (g w)) (![mood G i q,mood G i q]) (F w); have he:=disk_brief (gran Q) U A X (joined _ _ F h)
    unfold pia lux; simp_rw [cue_at, lawn, flee_run]; exact he
lemma cog_neap : let A:TresF (Fin 2):= ![step d,-step d]; let Z:=fun w=> molt 0 (![mood G i q,mood G i q]) (F w);
    Rose L (fun w=>cob d i q (F w)) (fun w=> neap 2 (Z w) 0 A):=by
    intro A Z; let X:TresF (Fin 2):= ![step d,-step d];
    have he:=pan_brief (gran Q) Z A (joined _ _ F h);
    unfold cob; simp_rw[clue_at d i q d (F _),cue_at,lawn,flee_run]; simp only [Int.cast_zero,zero_smul,add_zero];exact he
end limit
-- finite relations for addition and root shifts.
variable {F H:Maze G f}
lemma clip_eq (he:iteratedFDeriv ℝ 2 F 0=iteratedFDeriv ℝ 2 H 0) (x y:Site f): clipP i q F x y=clipP i q H x y:=by unfold clipP beat; rw [he]
lemma clip_add (x y:Site f)(h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0):clipP i q (F+H) x y= clipP i q F x y+clipP i q H x y:=by
    have hx: beat (F+H) 0 2=beat F 0 2+beat H 0 2:=by
        apply enlarge_unique; intro v; rw [_root_.add_apply,beat_real,beat_real,beat_real,iteratedFDeriv_add_apply (h.of_le le_top) (p.of_le le_top), _root_.add_apply]; simp
    unfold clipP; rw[hx];rfl
lemma clip_smul (x y:Site f)(h:ContDiffAt ℝ ω F 0)(t:ℝ): clipP i q (t • F) x y=(t:ℂ)*clipP i q F x y:=by
    have ht: beat (t • F) 0 2=(t:ℂ) • beat F 0 2:=by
        apply enlarge_unique; intro v; rw[_root_.smul_apply, beat_real, beat_real, iteratedFDeriv_const_smul_apply (h.of_le le_top),_root_.smul_apply]; simp
    unfold clipP; rw[ht]; rfl
lemma clip_sub (x y:Site f)(h:ContDiffAt ℝ ω F 0)(p:ContDiffAt ℝ ω H 0):clipP i q (F-H) x y=clipP i q F x y-clipP i q H x y:=by
    rw[sub_eq_add_neg, show -H=(-1:ℝ) • H from (neg_one_smul ..).symm,clip_add _ _ _ _ h (show ContDiffAt ℝ ω ((-1:ℝ) • H) 0 from p.const_smul (-1:ℝ)), clip_smul i q _ _ p]; push_cast;ring
lemma clip_rot (x y z:Site f)(h:ContDiffAt ℝ ω F 0): clipP i q (F ∘ rideC z) x y=cell (x+y) z*clipP i q F x y:=by
    let A:= rideC (G:=G) z
    let L: Phase (Lines G f 1)→ₗ[ℂ] Phase (Lines G f 1):= LinearMap.pi fun i=> LinearMap.proj (rideI z i)
    have hp(u:Site f): L (relay u (mood G i q))=cell u z • relay u (mood G i q):=by ext1 i; change (cell u (i.1+z))*_=cell u z* (cell u i.1*_); rw [cell_add]; ring_nf; rfl
    have he:=evaluated (L:= A) (f:=F) L (fun _=>rfl) h.analyticAt (n:=2)
    unfold clipP; rw [he, MultilinearMap.compLinearMap_apply]; rw [show (fun j => L ((![_ ,_] :Fin 2 → Phase (Lines G f 1)) j))=(fun b=>(![cell x z,cell y z]: Fin 2 →ℂ) b • ((![relay x (mood G i q),relay y (mood G i q)]:Fin 2 → Phase (Lines G f 1)) b)) from ?_]
    rw[MultilinearMap.map_smul_univ]; simp[Fin.prod_univ_two, mul_cell]
    ext1 b; fin_cases b;exact hp _; exact hp _
end YM.Trace.Lamp
