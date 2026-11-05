import YM.TraceExtension.Loft.Samen
set_option autoImplicit false
/-!
# ROOTED Fourier contraction. Unlike per-cell logs, no translational sum
at the Oil vertex, hence independent routes for ± marked inputs.
-/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W α β:Type}[Fintype α][DecidableEq α]{g:W→Side}{L:Filter W}{G:Gauge}{f:Side}{p:Clip}{k m n:ℕ}
abbrev pom (p:Site f)(i:α)(M:CircM f α α):= dotProduct (relay (-p) i) (M *ᵥ relay p i)
def sip (z:Site f): Track:= pitchf f • reel (lift z)
lemma sip_roll (z:Site f) : rolls (mon z) (axes (sip z)):=by have h:=reel_roll f (lift z);rwa[wrap_lift] at h
lemma pom_w (M:CircM f α α): trace M= (Fintype.card (Site f):ℂ)⁻¹ *∑ k: Site f,∑ i:α, pom k i M:=by
    let R:= rotations f α; let N:ℂ:=Fintype.card (Site f)
    have h:R* star R=N • 1:=by rw[show N=(f.val:ℂ)^(4:ℕ) by simp[N]]; exact rotations_gram ..
    have he: (star R * (M*R)).trace=(∑ k:Site f,∑ i:α,pom k i M):=by
       rw[trace,Fintype.sum_prod_type]; refine sum_congr rfl (fun k _=>sum_congr rfl (fun i _=>?_)); change (star R*(M*R)) (k,i) (k,i)=_
       have hM(v:Co f α): R v (k,i)=relay k i v:=coef_wave ..
       unfold pom; rw[Matrix.mul_apply]; refine sum_congr rfl fun j _=>?_
       have hu: star R (k,i) j= relay (-k) i j :=by
           change star (R j (k,i))=_; rw [hM]; unfold relay tune; rw [star_mul',Complex.star_def,cell_bar, cell_duality (-k), cell_inverse,cell_duality j.1]; by_cases he:j.2=i <;>simp [he]
       rw[hu,Matrix.mul_apply]; change _= relay (-k) i j*(∑ x, M j x*(relay k i x)); simp_rw[hM]
    rw [trace_mul_comm, Matrix.mul_assoc M,h,Matrix.mul_smul,mul_one, trace_smul,smul_eq_mul] at he
    rw [← he, inv_mul_cancel_left₀ (show N≠0 from Nat.cast_ne_zero.mpr Fintype.card_pos.ne')]
lemma pom_pair (p:Site f) (i:α) (M N:CircM f α α) (V:Momentum → CompM α α)(s:Site f) (h:Jaunt N V s) : pom p i (M*N)=∑ j:α,(dotProduct (relay (-p) i) (M *ᵥ relay (p+s) j)) * V (axes (sip p)) j i:=by
    have hc: N *ᵥ relay p i=tune (p+s) (V (axes (sip p))*ᵥ Pi.single i 1):= h p _ (sip_roll p) _
    have hp: N*ᵥ relay p i= ∑ j:α, V (axes (sip p)) j i •relay (p+s) j:=by rw[hc]; ext1 j; rw[Finset.sum_apply];simp [tune,relay,mulVec_single,Pi.single_apply,mul_comm]
    unfold pom;rw[←Matrix.mulVec_mulVec,hp, Matrix.mulVec_sum,dotProduct_sum]; apply sum_congr rfl fun i _=>?_; rw[Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul,mul_comm]
abbrev TubeF (G:Gauge) (k:ℕ):=Film (Fslot G) (Loc G k) (Loc G k)
abbrev Land := TresF (Fin 2)
variable {F H:WildM G f k k}{V:TubeF G k}
def moss (V: TubeF G k)(F: WildM G f k k)(z:Track)(a:Fslot G)(i j:Loc G k)(x:Land):ℂ:=
    let p:=x 0; let q:= x 1; let K:= axes z
    carb 0 F i j ![a,a] ((x,z),-z) * V.tab K j i+
    carb 0 F i j ![a] ((![q],z+p),-z) * V.spot a (axes p) K j i+
    carb 0 F i j ![a] ((![p],z+q),-z) * V.spot a (axes q) K j i+
    carb 0 F i j (![]:Fin 0→_) ((![],z+(p+q)),-z) * V.arch a a (axes p) (axes q) K j i
lemma axes_add (x y:Track):axes (x+y)=axes x+axes y:=by ext1 i; simp[axes]
private lemma sled_o {p:Site f}(x:Track)(h:rolls (mon p) (axes x))(i:Loc G k): barca (0:Site f) x i=relay p i:=by ext1 j; unfold barca relay tune; rw[sub_zero, ← h.exp]; by_cases hp:j.2=i <;> simp [hp,cell]
lemma surf (h: Ticket V H)(hp: Memo F 0)(d s z: Site f)(x:Land)(i:Loc G k)(a:Fslot G) (hd:rolls (mon d) (axes (x 0)))(hs:rolls (mon s) (axes (x 1))):
   pom z i (cart (fun u=> F u*H u) (relay d a) (relay s a))=∑ j,moss V F (sip z) a i j x:=by
    let p:=x 0; let q:=x 1; let b:=sip z
    have ha(i:Loc G k):relay z i=barca 0 b i:= (sled_o _ (sip_roll z) _).symm
    have hN: relay (-z) i=barca 0 (-b) i:=by rw[sled_o _ (show rolls _ _ from ?_)]; rw[axes_flip]; exact (sip_roll z).flip_sign
    have h1(j:Loc G k): relay (z+d) j=barca 0 (b+p) j:=(sled_o _ (by rw[axes_add]; exact (sip_roll z).combine hd) _).symm
    have h2(j:Loc G k): relay (z+s) j=barca 0 (b+q) j:=(sled_o _ (by rw[axes_add];exact (sip_roll z).combine hs) _).symm
    have h3(j:Loc G k): relay (z+(d+s)) j=barca 0 (b+(p+q)) j:=(sled_o _ (by rw[axes_add,axes_add];exact (sip_roll z).combine (hd.combine hs)) _).symm
    have hv(A B:CircM f (Loc G k) (Loc G k)): pom z i (A+B)=pom z i A+pom z i B:=by rw[pom,add_mulVec,dotProduct_add]
    rw [cart_prod hp h.finance]; simp_rw[hv]; rw [pom_pair _ _ _ _ _ _ h.tab, pom_pair _ _ _ _ _ _ (h.spot a d _ hd),pom_pair _ _ _ _ _ _ (h.spot a s _ hs),pom_pair _ _ _ _ _ _ (h.arch _ _ _ _ _ _ hd hs), add_zero, ← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]; refine sum_congr rfl fun j _=>?_; rw [ha,hN,h1,h2,h3]
    unfold moss carb; dsimp only; rw [show relay d a=barca (0:Site f) p a from (sled_o _ hd _).symm, show relay s a=barca (0:Site f) q a from (sled_o _ hs _).symm]
    unfold cart seat; rw[show (![barca (0:Site f) p a,barca 0 q a] :Fin 2→ Phase (Lines G f 1))= _ from (show _=fun j:Fin 2=> barca 0 (x j) ((![a,a]:Fin 2 →_) j) from funext fun j=>by fin_cases j <;> rfl)]
    have he(w:Track): (![barca (0:Site f) w a]:Fin 1→ Phase (Lines G f 1))=(fun j:Fin 1=>barca 0 ((![w]: Fin 1→_) j) ((![a]:Fin 1→_) j)):=funext fun j=>by fin_cases j; rfl
    rw[he,he,show cardM F= art F 0 (![]:Fin 0→ Phase (Lines G f 1)) from (art_zero F).symm]; congr 5; exact Subsingleton.elim ..
abbrev fern (V:TubeF G k)(F:WildM G f k k)(a:Fslot G)(x:Track)(p:Land):ℂ:=∑ i, ∑ j,moss V F x a i j p
abbrev Pond (F:WildM G f k k)(a:Fslot G)(V: TubeF G k)(x:Land):ℂ:= (Fintype.card (Site f):ℂ)⁻¹ * ∑ z:Site f,fern V F a (sip z) x
lemma cusp (d i b:Axis)(q:G.ColorIndex)(h:Ticket V H)(hp:Memo F 0)(t:Dish): cue d i q b (fun x=> (H x*F x).trace) t=Pond F (mood G i q) V (pitchf f • lawn d b t):=by
   let T:= pitchf f; rw [show (fun x=>(H x*F x).trace)=(fun x=>(F x*H x).trace) from funext fun i=> trace_mul_comm ..]; unfold cue clipP; rw[cart_trace (hp.cross h.finance),pom_w]; unfold Pond; apply congr_arg _; apply sum_congr rfl fun w _=>?_
   rw[reeling]; unfold fern; apply sum_congr rfl fun i _=>?_; apply surf h hp <;> exact reel_roll ..
end YM.Trace.Loft
